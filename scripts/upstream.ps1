# Upstream Effekt test corpus.
#
# `testdata/upstream/examples` is a verbatim copy of the Effekt repository's
# `examples/pos`, `examples/stdlib` and `examples/neg` directories (see
# `testdata/upstream/README.md`). Every positive test has a `.check` file with
# the program's expected stdout; the negative tests describe the expected
# diagnostics either in a `.check` file or in `// ERROR` / `// WARN` comments.
#
#   pos, stdlib   compile and run; stdout has to match `.check`
#   benchmarks    the same, in the benchmarks' test mode (no argument)
#   casestudies   the same, for literate `.effekt.md` programs
#   noopt         upstream's `withoutOptimizations` list: the same programs
#                 compiled with `--no-optimize`, against the same `.check`
#   neg           compilation has to fail and report a diagnostic of the
#                 expected severity on the expected line
#
# The baseline can only grow: raise it after every improvement, never lower it
# without removing a test. Re-syncing the corpus to a newer upstream re-bases it
# (that is a new set of tests, not a regression); the numbers and the reason are
# recorded in the commit message and in `testdata/upstream/README.md`.
#
# Usage: powershell -File scripts/upstream.ps1 [-Filter <substring>] [-ShowWording] [-Strict]

param(
  [string]$Filter = "",
  [switch]$ShowWording,
  # Compare the *whole* rendered diagnostics of a negative test that has a
  # `.check` file, the way upstream's `assertNoDiff` does. This is stricter than
  # the wording check (which mirrors `validateErrors`: severity, line, and the
  # expected text somewhere in the message); it is reported, not enforced.
  [switch]$Strict
)

$ErrorActionPreference = "Continue"
$root = Split-Path -Parent $PSScriptRoot
Push-Location $root

# Compiling one file loads the whole prelude, so the corpus is split across a
# few background jobs to keep the wall-clock time reasonable.
$jobs = 6
$positiveBaseline = 441
# Every negative test matches: severity and line as `EffektTests.scala` does for
# the tests that only carry `// ERROR` comments, and the wording of all of them
# (`-ShowWording` reports any that differ). `-Strict` additionally compares the
# whole rendered diagnostic of the tests that carry a `.check` file; the
# baseline counts the ones whose full text is identical to upstream's.
$negativeBaseline = 243
$negativeStrictBaseline = 240
# `examples/benchmarks` is the third positive suite upstream runs on the JS
# backend. Every benchmark runs in *test mode* (no command-line argument, see
# `benchmarks/runner.effekt`): it computes a small result and prints it, which
# is what the `.check` file records. The `config_*.txt` files upstream uses to
# benchmark are not read here.
$benchmarkBaseline = 91
# `examples/casestudies` is literate: every `.effekt.md` there is a program whose
# code fences the compiler extracts, with a `.check` file holding its output.
$casestudyBaseline = 10
# Upstream also compiles a handful of programs with `--no-optimize` and compares
# them against the *same* `.check` file (`EffektTests.runWithoutOptimizations`):
# the optimizer is not allowed to change what a program prints.
$noOptimizationBaseline = 7

Write-Host "building the compiler..." -ForegroundColor Cyan
moon build --target js 2>&1 | Out-Null
if ($LASTEXITCODE -ne 0) { Pop-Location; exit 1 }

$cli = Join-Path $root "_build/js/debug/build/cmd/main/main.js"
$libDir = Join-Path $root "libraries"

# A run that does not finish cleanly (Ctrl-C, a killed job, an editor restarting
# the script) leaves the compiler of the files that were still running behind:
# `Invoke-Effekt` kills the `cmd.exe` wrapper on a timeout, and the `node`
# grandchild survives it — and a program that loops in the compiler never exits
# on its own. Such a leftover keeps burning a core and holds the redirect files
# of its test, which is what silently turned every later run's comparison for
# that test into "output differs". They are recognisable by their command line
# (they all name this checkout's `main.js`), so the run starts by clearing them.
function Stop-StrayCompilers() {
  $killed = 0
  foreach ($process in (Get-CimInstance Win32_Process -Filter "Name='node.exe'" -ErrorAction SilentlyContinue)) {
    if ($process.CommandLine -and $process.CommandLine.Contains($cli)) {
      & taskkill /F /T /PID $process.ProcessId 2>&1 | Out-Null
      $killed++
    }
  }
  return $killed
}

$stray = Stop-StrayCompilers
if ($stray -gt 0) {
  Write-Host "killed $stray compiler process(es) left over by an earlier run" -ForegroundColor Yellow
}

$corpus = Join-Path $root "testdata/upstream"
$outDir = Join-Path $root ".upstream-out"
if (Test-Path $outDir) {
  Remove-Item -Recurse -Force $outDir -ErrorAction SilentlyContinue
  if (Test-Path $outDir) {
    Write-Host "cannot remove $outDir; a compiler process still holds it" -ForegroundColor Red
    Pop-Location
    exit 1
  }
}
New-Item -ItemType Directory -Force $outDir | Out-Null

# ---------------------------------------------------------------------------
# The worker: run one test file and report a single line per test.
#
# Emits `<kind>\t<status>\t<relative path>\t<detail>` lines, where kind is
# `pos`, `bench`, `case`, `noopt` or `neg` and status is `ok`, `fail`, or
# `wording`.
# ---------------------------------------------------------------------------
$worker = {
  param($cli, $libDir, $corpus, $outDir, $files, $strict)

  # `Start-Job` workers do not inherit the working directory.
  Set-Location (Split-Path -Parent (Split-Path -Parent $corpus))

  # Runs the compiler on one file with a timeout. `Start-Process` is used
  # instead of `& node ... 2> file`: PowerShell wraps a native command's stderr
  # in error records (script line, category, 80-column wrapping), which destroys
  # the diagnostics, and it cannot interrupt a program that does not terminate.
  # The exit code is written to a file by a small batch wrapper: a `Process`
  # object returned by `Start-Process` inside a background job is deserialized,
  # so `ExitCode` is not available there.
  function Invoke-Effekt($file, $jsOut, $run, $relFile, $noOpt, [int]$timeoutMs = 30000) {
    $stdoutFile = "$jsOut.out"
    $stderrFile = "$jsOut.err"
    $codeFile = "$jsOut.code"
    $batchFile = "$jsOut.cmd"
    $runArg = if ($run) { " --run" } else { "" }
    $optArg = if ($noOpt) { " --no-optimize" } else { "" }
    # The compiler runs from the corpus root with the path *relative* to it, as
    # upstream does: `sourcePosition` embeds the path it is given, and the
    # recorded `.check` files contain the upstream layout (`examples/pos/...`).
    $batch = "@echo off`r`n" +
      "cd /d `"$corpus`"`r`n" +
      "node `"$cli`" --lib `"$libDir`" -I `"$corpus`" -o `"$jsOut`"$runArg$optArg `"$relFile`" 1> `"$stdoutFile`" 2> `"$stderrFile`"`r`n" +
      "> `"$codeFile`" echo %ERRORLEVEL%`r`n"
    [IO.File]::WriteAllText($batchFile, $batch)
    # `-WindowStyle Hidden` keeps the hundreds of per-test console windows from
    # flashing up while the corpus runs.
    $p = Start-Process -FilePath "cmd.exe" -ArgumentList "/c", "`"$batchFile`"" -PassThru -WindowStyle Hidden
    $finished = $p.WaitForExit($timeoutMs)
    if (-not $finished) {
      # Kill the whole tree. `$p` is the `cmd.exe` wrapper; killing only it left
      # `node` running, and a program that loops inside the compiler never
      # terminates, so every timeout leaked one busy core and the files it held
      # (see `Stop-StrayCompilers`).
      & taskkill /F /T /PID $p.Id 2>&1 | Out-Null
      try { $p.Kill() } catch { }
      return @{ code = -1; timeout = $true; stdout = ""; stderr = "" }
    }
    $code = -1
    if (Test-Path $codeFile) {
      $text = (Read-Text-WithRetry $codeFile).Trim()
      if ($text -match '^-?\d+$') { $code = [int]$text }
    }
    # Empty output files make `Get-Content -Raw` return an empty array, so the
    # content is read directly and kept as a string.
    $so = Read-Text-WithRetry $stdoutFile
    $se = Read-Text-WithRetry $stderrFile
    # `json.effekt` prints a string that contains a lone carriage return
    # (`readQuotedString` turns the `\r` escape into CR).  Upstream records the
    # output by splitting it into lines with `readLine`, which treats a lone CR
    # as a line terminator too, so the `.check` file has a line break there.
    # Normalising CR and CRLF to LF reproduces the recording.
    return @{
      code = $code
      timeout = $false
      stdout = (($so -replace "`r`n", "`n") -replace "`r", "`n")
      stderr = (($se -replace "`r`n", "`n") -replace "`r", "`n")
    }
  }

  # Reads a file the compiler may still be flushing while the run is killed.
  # `Invoke-Effekt` kills the whole process tree on a timeout, but `node` closes
  # its redirect files asynchronously, so a read can still hit
  # "The process cannot access the file"; retry briefly. An unreadable file
  # reads as empty.
  function Read-Text-WithRetry($path) {
    if (-not (Test-Path $path)) { return "" }
    for ($attempt = 0; $attempt -lt 20; $attempt++) {
      try {
        return [IO.File]::ReadAllText($path)
      } catch {
        Start-Sleep -Milliseconds 100
      }
    }
    return ""
  }

  # The severity/line/message triples of our own diagnostics. The rendering is
  # upstream's (`[error] path:line:column message`, see `Message::render`), and
  # the message is everything up to the source excerpt: `FailedOverloadError`
  # and friends nest further messages below the first line, and upstream's
  # `validateErrors` searches the whole formatted message, not just its first
  # line.
  function Get-Diagnostics($text) {
    $diags = @()
    # Split before every diagnostic header, keeping the header with its block.
    foreach ($part in [regex]::Split($text, '(?m)^(?=\[(?:error|warning|info)\]\s)')) {
      if ($part -notmatch '^\[(error|warning|info)\]\s+\S+?:(\d+):(\d+):?\s*([\s\S]*)$') { continue }
      $body = ($Matches[4] -split "`n")
      # The excerpt is the source line plus the caret line; a missing span has
      # none.
      if ($body.Count -ge 2 -and $body[$body.Count - 1] -match '^\s*\^+\s*$') {
        $body = $body[0..($body.Count - 3)]
      }
      $diags += @{
        severity = $Matches[1]
        line = [int]$Matches[2]
        text = (($body -join "`n").Trim())
      }
    }
    return ,$diags
  }

  # Everything the compiler reported, as one block of text: the diagnostics are
  # what upstream appends to a positive test's output in its `.check` file (it
  # writes the program's stdout and the buffered messages into the same
  # emitter). The `Wrote ...` line of our CLI is not part of it.
  function Get-DiagnosticText($text) {
    $lines = $text -split "`n"
    $start = -1
    for ($i = 0; $i -lt $lines.Count; $i++) {
      if ($lines[$i] -match '^\[(error|warning|info)\]') { $start = $i; break }
    }
    if ($start -lt 0) { return "" }
    $kept = $lines[$start..($lines.Count - 1)] | Where-Object { -not $_.StartsWith("Wrote ") }
    return ($kept -join "`n")
  }

  # The `.check` files are plain text: upstream writes them with
  # `removeAnsiColors` ("We remove ansi colors to make check files
  # human-readable"), so the ANSI SGR escapes the standard library's `Formatted`
  # output contains have to be dropped before comparing, too.
  function Remove-AnsiColors([string]$text) {
    return [regex]::Replace($text, "\u001b\[[;\d]*m", "")
  }

  # The `.check` file of a test: `foo.effekt` and the literate `foo.effekt.md`
  # both record their output in `foo.check` (upstream `checkFileFor`).
  function Get-CheckFile($file) {
    if ($file.EndsWith(".effekt.md")) {
      $file.Substring(0, $file.Length - ".effekt.md".Length) + ".check"
    } else {
      [IO.Path]::ChangeExtension($file, ".check")
    }
  }

  # The expected diagnostics of a negative test: from the `.check` file when
  # there is one, otherwise from the `// ERROR` / `// WARN` comments.
  function Get-Expected($file) {
    $expected = @()
    $check = Get-CheckFile $file
    if (Test-Path $check) {
      foreach ($line in (Get-Content $check)) {
        if ($line -match '^\[(error|warning|info)\]\s+\S+?:(\d+):(\d+):\s*(.*)$') {
          $expected += @{ severity = $Matches[1]; line = [int]$Matches[2]; text = ($Matches[4] -replace '\s*\[[a-z]+\]\s*$', '').Trim() }
        }
      }
    } else {
      $no = 0
      foreach ($line in (Get-Content $file)) {
        $no++
        if ($line -match '//\s*(ERROR|WARN)\s*(.*)$') {
          $severity = if ($Matches[1] -eq 'ERROR') { 'error' } else { 'warning' }
          $expected += @{ severity = $severity; line = $no; text = $Matches[2].Trim() }
        }
      }
    }
    return ,$expected
  }

  foreach ($item in $files) {
   try {
    $file = $item.file
    $kind = $item.kind
    $rel = $item.rel
    # A program may be compiled twice (with and without the optimizer), so the
    # scratch output carries the kind as well.
    $jsOut = Join-Path $outDir ("{0}.{1}.js" -f ($rel -replace '[\\/]', '__'), $kind)

    if ($kind -eq "pos" -or $kind -eq "bench" -or $kind -eq "case" -or $kind -eq "noopt") {
      $noOpt = ($kind -eq "noopt")
      $check = Get-CheckFile $file
      $expected = ""
      if (Test-Path $check) {
        $expected = ([IO.File]::ReadAllText($check)).Replace("`r`n", "`n").TrimEnd()
      }
      $r = Invoke-Effekt $file $jsOut $true $rel $noOpt
      if ($r.timeout) {
        # the corpus runs six files at a time; a slow machine can push one over
        # the limit, so a timeout is retried once before it is reported
        $r = Invoke-Effekt $file $jsOut $true $rel $noOpt 60000
      }
      if ($r.timeout) {
        "$kind`tfail`t$rel`ttimeout (90s)"
      } else {
        # The program's output followed by the compiler's diagnostics, exactly
        # what upstream recorded in the `.check` file. A test whose check file
        # only contains diagnostics (`bidirectional/selfrecursion` reports an
        # unsupported feature) compares equal here even though the program does
        # not run.
        $actual = (Remove-AnsiColors $r.stdout).TrimEnd()
        $diagText = (Remove-AnsiColors (Get-DiagnosticText $r.stderr)).TrimEnd()
        if ($diagText -ne "") { if ($actual -eq "") { $actual = $diagText } else { $actual = "$actual`n$diagText" } }
        if ($actual -eq $expected) {
          "$kind`tok`t$rel`t"
        } elseif ($r.code -ne 0) {
          $first = ($r.stderr -split "`n" | Where-Object { $_ -match '^\[(error|warning|info)\]' } | Select-Object -First 1)
          if ($first) {
            "$kind`tfail`t$rel`t$first"
          } else {
            # The compiler succeeded, so the program itself failed: report the
            # exception node threw (the first line of the stack trace that names
            # it), not the `Wrote ...` line of the compiler.
            $detail = ($r.stderr -split "`n" | Where-Object { $_ -match '(Error|error)' -and $_ -notmatch '^Wrote ' } | Select-Object -First 1)
            if (-not $detail) {
              $detail = ($r.stderr -split "`n" | Where-Object { $_.Trim() -ne "" } | Select-Object -Last 1)
            }
            "$kind`tfail`t$rel`truntime: $detail"
          }
        } else {
          "$kind`tfail`t$rel`toutput differs"
        }
      }
    } else {
      $expected = Get-Expected $file
      # Upstream's `runNegativeTestsIn` calls `run(f, true)`, i.e. it *runs* a
      # negative test that has a `.check` file as well — the file records the
      # program's output (a test may only warn) followed by the diagnostics.
      $r = Invoke-Effekt $file $jsOut $true $rel $false
      if ($r.timeout) {
        $r = Invoke-Effekt $file $jsOut $true $rel $false 60000
      }
      if ($r.timeout) {
        "$kind`tfail`t$rel`ttimeout (90s)"
        continue
      }
      $diags = Get-Diagnostics $r.stderr
      $missing = @()
      $wording = 0
      $wordingDetails = @()
      foreach ($e in $expected) {
        # Every diagnostic with that severity on that line is fair game: a line
        # can carry several messages (a match arm mismatch explains both the
        # merged arms and the component that differed), and upstream's
        # `validateErrors` searches all of them for the expected text.
        $candidates = @($diags | Where-Object {
          $_.severity -eq $e.severity -and $_.line -eq $e.line
        })
        if ($candidates.Count -eq 0) {
          $missing += "$($e.severity) at line $($e.line)"
        } elseif ($e.text -ne "" -and -not ($candidates | Where-Object { $_.text.Contains($e.text) })) {
          $wording++
          $got = ($candidates | ForEach-Object { $_.text }) -join " / "
          $wordingDetails += "$($e.severity) line $($e.line): expected <$($e.text)> got <$got>"
        }
      }
      if ($missing.Count -gt 0) {
        "$kind`tfail`t$rel`tmissing: $($missing -join ', ')"
      } elseif ($expected.Count -eq 0 -and $r.code -eq 0) {
        "$kind`tfail`t$rel`tcompiled without an error"
      } elseif ($wording -gt 0) {
        "$kind`twording`t$rel`t$wording message(s) differ in wording: " + ($wordingDetails -join " | ")
      } elseif ($strict -and (Test-Path (Get-CheckFile $file))) {
        # Upstream's `runNegativeTestsIn` compares the recorded `.check` file
        # verbatim (`assertNoDiff`) when there is one. Report the first line that
        # differs, so the remaining work is visible one difference at a time.
        $check = Get-CheckFile $file
        $actualText = (Remove-AnsiColors $r.stdout).TrimEnd()
        $diagText = (Remove-AnsiColors (Get-DiagnosticText $r.stderr)).TrimEnd()
        if ($diagText -ne "") {
          if ($actualText -eq "") { $actualText = $diagText } else { $actualText = "$actualText`n$diagText" }
        }
        $expectedText = ([IO.File]::ReadAllText($check)).Replace("`r`n", "`n").TrimEnd()
        if ($actualText -eq $expectedText) {
          "$kind`tok`t$rel`t"
        } else {
          $a = $actualText -split "`n"
          $b = $expectedText -split "`n"
          $first = ""
          for ($i = 0; $i -lt [Math]::Max($a.Count, $b.Count); $i++) {
            $la = if ($i -lt $a.Count) { $a[$i] } else { "<missing>" }
            $lb = if ($i -lt $b.Count) { $b[$i] } else { "<missing>" }
            if ($la -ne $lb) {
              $first = "line $($i + 1): expected <$lb> got <$la>"
              break
            }
          }
          "$kind`tstrict`t$rel`t$first"
        }
      } else {
        "$kind`tok`t$rel`t"
      }
    }
   } catch {
     "$kind`tfail`t$rel`tEXC line $($_.InvocationInfo.ScriptLineNumber): $($_.Exception.Message)"
   }
  }
}

# ---------------------------------------------------------------------------
# Collect the tests and split them across the workers.
# ---------------------------------------------------------------------------
# Tests that cannot pass here, with the reason. `propagators` is in upstream's
# own ignore list for the JS backend (the `unsafe/cont` module it imports does
# not exist); the other two need POSIX paths or tools (writing to
# `/dev/stdout`, spawning `cat`) that Windows does not have, so upstream's CI
# passes them and this machine cannot. They stay in the corpus and are listed
# in the summary — only the pass counts leave them out.
$skipped = @{
  "examples/pos/propagators.effekt" = "ignored upstream: imports the missing module unsafe/cont"
  "examples/pos/issue1087.effekt" = "writes to /dev/stdout"
  "examples/stdlib/io/process.effekt" = "spawns the POSIX tool cat"
  "examples/stdlib/io/process_contract.effekt" = "spawns the POSIX tools sh and sleep"
  "examples/stdlib/io/spawn_options.effekt" = "spawns the POSIX tools sh, echo, seq and yes"
  "examples/benchmarks/folklore_to_fact/cps_tak.effekt" = "ignored upstream for JS: the continuation stack overflows"
  # `small_files` writes into `/tmp/small_files` and accepts only `-17` (EEXIST)
  # from `mkdir`: node reports libuv's `-4075` on Windows, so the benchmark
  # panics when the directory already exists. Upstream has the same problem on
  # Windows, its CI is POSIX.
  "examples/benchmarks/input_output/small_files.effekt" = "checks the POSIX EEXIST errno (-17) of mkdir"
}
$tests = @()
foreach ($dir in @("pos", "stdlib", "benchmarks")) {
  $base = Join-Path $corpus "examples/$dir"
  # The benchmark suite is its own kind so that its baseline can grow on its
  # own: a benchmark is a positive test, but it is also the only test that has
  # to survive a real workload.
  $kind = if ($dir -eq "benchmarks") { "bench" } else { "pos" }
  foreach ($f in (Get-ChildItem -Recurse $base -Filter '*.effekt' -File)) {
    $rel = $f.FullName.Substring($corpus.Length).TrimStart('\', '/') -replace '\\', '/'
    if ($Filter -ne "" -and -not $rel.Contains($Filter)) { continue }
    if ($skipped.ContainsKey($rel)) { continue }
    $tests += @{ kind = $kind; file = $f.FullName; rel = $rel }
  }
}
# The case studies are literate (`.effekt.md`) programs: the compiler extracts
# the code fences, keeping the lines of the markdown file (see the README).
$base = Join-Path $corpus "examples/casestudies"
foreach ($f in (Get-ChildItem -Recurse $base -Filter '*.effekt.md' -File)) {
  $rel = $f.FullName.Substring($corpus.Length).TrimStart('\', '/') -replace '\\', '/'
  if ($Filter -ne "" -and -not $rel.Contains($Filter)) { continue }
  if ($skipped.ContainsKey($rel)) { continue }
  $tests += @{ kind = "case"; file = $f.FullName; rel = $rel }
}
$base = Join-Path $corpus "examples/neg"
foreach ($f in (Get-ChildItem -Recurse $base -Filter '*.effekt' -File)) {
  $rel = $f.FullName.Substring($corpus.Length).TrimStart('\', '/') -replace '\\', '/'
  if ($Filter -ne "" -and -not $rel.Contains($Filter)) { continue }
  $tests += @{ kind = "neg"; file = $f.FullName; rel = $rel }
}
# Upstream's `withoutOptimizations` (`JavaScriptTests.scala`): these programs are
# also compiled with `--no-optimize` and compared against the same `.check` file.
# They are listed by hand, as upstream does, because the point is that this
# particular list keeps working without the optimizer.
$withoutOptimizations = @(
  # contifying under reset
  "examples/pos/issue842.effekt",
  "examples/pos/issue861.effekt",
  # contifying a block that is also passed as an argument
  "examples/pos/contify_block_used_as_value.effekt",
  "examples/pos/parser.effekt",
  "examples/pos/probabilistic.effekt",
  # local function def needs to be rewritten (issue 1229)
  "examples/benchmarks/folklore_to_fact/motzkin.effekt",
  # a local definition in a loop capturing a block parameter of the loop
  "examples/pos/loop_block_parameter.effekt"
)
foreach ($rel in $withoutOptimizations) {
  if ($Filter -ne "" -and -not $rel.Contains($Filter)) { continue }
  if ($skipped.ContainsKey($rel)) { continue }
  $tests += @{ kind = "noopt"; file = (Join-Path $corpus $rel); rel = $rel }
}

$chunks = @()
for ($i = 0; $i -lt $jobs; $i++) { $chunks += ,@() }
for ($i = 0; $i -lt $tests.Count; $i++) { $chunks[$i % $jobs] += $tests[$i] }

$start = Get-Date
$jobObjects = @()
foreach ($chunk in $chunks) {
  if ($chunk.Count -eq 0) { continue }
  $jobObjects += Start-Job -ScriptBlock $worker -ArgumentList $cli, $libDir, $corpus, $outDir, $chunk, $Strict
}
$results = $jobObjects | Wait-Job | Receive-Job
$jobObjects | Remove-Job
Write-Host ("compiled {0} test files in {1:N0}s" -f $tests.Count, ((Get-Date) - $start).TotalSeconds) -ForegroundColor DarkGray

# ---------------------------------------------------------------------------
# Summarize.
# ---------------------------------------------------------------------------
$posOk = 0
$posTotal = 0
$benchOk = 0
$benchTotal = 0
$caseOk = 0
$caseTotal = 0
$nooptOk = 0
$nooptTotal = 0
$negOk = 0
$negTotal = 0
$negWording = 0
$negWordingDetails = @()
$negStrictOk = 0
$negStrictTotal = 0
$negStrictDetails = @()
$failures = @{}

foreach ($line in $results) {
  if ($null -eq $line -or "$line" -eq "") { continue }
  $parts = "$line".Split("`t")
  if ($parts.Count -lt 4) { continue }
  $kind = $parts[0]
  $status = $parts[1]
  $rel = $parts[2]
  $detail = if ($parts.Count -gt 3) { $parts[3] } else { "" }
  if ($kind -eq "pos" -or $kind -eq "bench" -or $kind -eq "case" -or $kind -eq "noopt") {
    if ($kind -eq "bench") {
      $benchTotal++
    } elseif ($kind -eq "case") {
      $caseTotal++
    } elseif ($kind -eq "noopt") {
      $nooptTotal++
    } else {
      $posTotal++
    }
    if ($status -eq "ok") {
      if ($kind -eq "bench") {
        $benchOk++
      } elseif ($kind -eq "case") {
        $caseOk++
      } elseif ($kind -eq "noopt") {
        $nooptOk++
      } else {
        $posOk++
      }
    } else {
      if (-not $failures.ContainsKey($detail)) { $failures[$detail] = @() }
      $failures[$detail] += $rel
    }
  } else {
    $negTotal++
    if ($status -eq "strict") {
      # the test still matches by upstream's `validateErrors` criterion
      $negOk++
      if ($Strict) {
        $negStrictTotal++
        $negStrictDetails += "$rel`t$detail"
      }
    } elseif ($status -eq "ok") {
      $negOk++
      if ($Strict) { $negStrictTotal++; $negStrictOk++ }
    } elseif ($status -eq "wording") {
      $negOk++
      $negWording++
      $negWordingDetails += "$rel`t$detail"
    }
    else {
      if (-not $failures.ContainsKey($detail)) { $failures[$detail] = @() }
      $failures[$detail] += $rel
    }
  }
}

Write-Host ""
Write-Host ("positive (pos + stdlib): {0} of {1} pass" -f $posOk, $posTotal) -ForegroundColor Cyan
Write-Host ("benchmarks:              {0} of {1} run and match" -f $benchOk, $benchTotal) -ForegroundColor Cyan
Write-Host ("casestudies:             {0} of {1} run and match" -f $caseOk, $caseTotal) -ForegroundColor Cyan
Write-Host ("without optimizations:   {0} of {1} run and match" -f $nooptOk, $nooptTotal) -ForegroundColor Cyan
Write-Host ("negative (neg):          {0} of {1} match ({2} pass with different wording)" -f $negOk, $negTotal, $negWording) -ForegroundColor Cyan
if ($Strict) {
  Write-Host ("  of those, full text:   {0} of {1} `.check` files match exactly" -f $negStrictOk, $negStrictTotal) -ForegroundColor Cyan
}
if ($skipped.Count -gt 0) {
  Write-Host ("skipped:                 {0} tests that cannot pass on this platform" -f $skipped.Count) -ForegroundColor DarkGray
  foreach ($name in ($skipped.Keys | Sort-Object)) { Write-Host ("           $name ({0})" -f $skipped[$name]) -ForegroundColor DarkGray }
}

if ($ShowWording -and $negWordingDetails.Count -gt 0) {
  Write-Host ""
  Write-Host "negative tests whose wording differs (expected <>, got <>):" -ForegroundColor Yellow
  foreach ($entry in $negWordingDetails) {
    $parts = $entry.Split("`t")
    Write-Host ("  {0}" -f $parts[0])
    Write-Host ("    {0}" -f $parts[1]) -ForegroundColor DarkGray
  }
}

if ($Strict -and $negStrictDetails.Count -gt 0) {
  Write-Host ""
  Write-Host "negative tests whose full diagnostic text differs (first differing line):" -ForegroundColor Yellow
  foreach ($entry in $negStrictDetails) {
    $parts = $entry.Split("`t")
    Write-Host ("  {0}" -f $parts[0])
    Write-Host ("    {0}" -f $parts[1]) -ForegroundColor DarkGray
  }
}

if ($failures.Count -gt 0) {
  Write-Host ""
  Write-Host "failures by cause:" -ForegroundColor Yellow
  $sorted = $failures.Keys | Sort-Object { $failures[$_].Count } -Descending
  foreach ($cause in $sorted) {
    $list = $failures[$cause]
    Write-Host ("{0,5}  {1}" -f $list.Count, $cause)
    foreach ($f in ($list | Select-Object -First 5)) { Write-Host "       $f" -ForegroundColor DarkGray }
    if ($list.Count -gt 5) { Write-Host ("       ... and {0} more" -f ($list.Count - 5)) -ForegroundColor DarkGray }
  }
}

Pop-Location

$failed = $false
# A `-Filter` run only compiles a handful of files, so it can never reach the
# baseline; it reports its own results and only a full run enforces one.
if ($Filter -ne "") {
  Write-Host ""
  Write-Host ("filtered run (no baseline check): {0}/{1} positive, {2}/{3} benchmarks, {4}/{5} casestudies, {6}/{7} without optimizations, {8}/{9} negative" -f $posOk, $posTotal, $benchOk, $benchTotal, $caseOk, $caseTotal, $nooptOk, $nooptTotal, $negOk, $negTotal) -ForegroundColor DarkGray
} else {
  if ($posOk -lt $positiveBaseline) {
    Write-Host ("positive: {0} pass, below the baseline of {1}" -f $posOk, $positiveBaseline) -ForegroundColor Red
    $failed = $true
  }
  if ($benchOk -lt $benchmarkBaseline) {
    Write-Host ("benchmarks: {0} pass, below the baseline of {1}" -f $benchOk, $benchmarkBaseline) -ForegroundColor Red
    $failed = $true
  }
  if ($caseOk -lt $casestudyBaseline) {
    Write-Host ("casestudies: {0} pass, below the baseline of {1}" -f $caseOk, $casestudyBaseline) -ForegroundColor Red
    $failed = $true
  }
  if ($nooptOk -lt $noOptimizationBaseline) {
    Write-Host ("without optimizations: {0} pass, below the baseline of {1}" -f $nooptOk, $noOptimizationBaseline) -ForegroundColor Red
    $failed = $true
  }
  if ($negOk -lt $negativeBaseline) {
    Write-Host ("negative: {0} match, below the baseline of {1}" -f $negOk, $negativeBaseline) -ForegroundColor Red
    $failed = $true
  }
  if ($Strict -and $negStrictOk -lt $negativeStrictBaseline) {
    Write-Host ("negative (full text): {0} match, below the baseline of {1}" -f $negStrictOk, $negativeStrictBaseline) -ForegroundColor Red
    $failed = $true
  }
  if ($failed) { exit 1 }
  $baselines = "baselines: positive {0}, benchmarks {1}, casestudies {2}, without optimizations {3}, negative {4}" -f $positiveBaseline, $benchmarkBaseline, $casestudyBaseline, $noOptimizationBaseline, $negativeBaseline
  if ($Strict) { $baselines += ", negative (full text) {0}" -f $negativeStrictBaseline }
  Write-Host $baselines -ForegroundColor Green
}
