# Upstream Effekt test corpus.
#
# `testdata/upstream/examples` is a verbatim copy of the Effekt repository's
# `examples/pos`, `examples/stdlib` and `examples/neg` directories (see
# `testdata/upstream/README.md`). Every positive test has a `.check` file with
# the program's expected stdout; the negative tests describe the expected
# diagnostics either in a `.check` file or in `// ERROR` / `// WARN` comments.
#
#   pos, stdlib   compile and run; stdout has to match `.check`
#   neg           compilation has to fail and report a diagnostic of the
#                 expected severity on the expected line
#
# The baseline can only grow: raise it after every improvement, never lower it
# without removing a test.
#
# Usage: powershell -File scripts/upstream.ps1 [-Filter <substring>]

param(
  [string]$Filter = ""
)

$ErrorActionPreference = "Continue"
$root = Split-Path -Parent $PSScriptRoot
Push-Location $root

# Compiling one file loads the whole prelude, so the corpus is split across a
# few background jobs to keep the wall-clock time reasonable.
$jobs = 6
$positiveBaseline = 345
# `boxed-captures` (neg) compiles now that name-based implicit arguments exist: it
# needs the capture-set check that this port deliberately keeps coarse (see the
# "Deviations from upstream" section of the README). It stays in the corpus.
$negativeBaseline = 111

Write-Host "building the compiler..." -ForegroundColor Cyan
moon build --target js 2>&1 | Out-Null
if ($LASTEXITCODE -ne 0) { Pop-Location; exit 1 }

$cli = Join-Path $root "_build/js/debug/build/cmd/main/main.js"
$libDir = Join-Path $root "libraries"
$corpus = Join-Path $root "testdata/upstream"
$outDir = Join-Path $root ".upstream-out"
if (Test-Path $outDir) { Remove-Item -Recurse -Force $outDir -ErrorAction SilentlyContinue }
New-Item -ItemType Directory -Force $outDir | Out-Null

# ---------------------------------------------------------------------------
# The worker: run one test file and report a single line per test.
#
# Emits `<kind>\t<status>\t<relative path>\t<detail>` lines, where kind is
# `pos` or `neg` and status is `ok`, `fail`, or `wording`.
# ---------------------------------------------------------------------------
$worker = {
  param($cli, $libDir, $corpus, $outDir, $files)

  # `Start-Job` workers do not inherit the working directory.
  Set-Location (Split-Path -Parent (Split-Path -Parent $corpus))

  # Runs the compiler on one file with a timeout. `Start-Process` is used
  # instead of `& node ... 2> file`: PowerShell wraps a native command's stderr
  # in error records (script line, category, 80-column wrapping), which destroys
  # the diagnostics, and it cannot interrupt a program that does not terminate.
  # The exit code is written to a file by a small batch wrapper: a `Process`
  # object returned by `Start-Process` inside a background job is deserialized,
  # so `ExitCode` is not available there.
  function Invoke-Effekt($file, $jsOut, $run, $relFile, [int]$timeoutMs = 30000) {
    $stdoutFile = "$jsOut.out"
    $stderrFile = "$jsOut.err"
    $codeFile = "$jsOut.code"
    $batchFile = "$jsOut.cmd"
    $runArg = if ($run) { " --run" } else { "" }
    # The compiler runs from the corpus root with the path *relative* to it, as
    # upstream does: `sourcePosition` embeds the path it is given, and the
    # recorded `.check` files contain the upstream layout (`examples/pos/...`).
    $batch = "@echo off`r`n" +
      "cd /d `"$corpus`"`r`n" +
      "node `"$cli`" --lib `"$libDir`" -I `"$corpus`" -o `"$jsOut`"$runArg `"$relFile`" 1> `"$stdoutFile`" 2> `"$stderrFile`"`r`n" +
      "> `"$codeFile`" echo %ERRORLEVEL%`r`n"
    [IO.File]::WriteAllText($batchFile, $batch)
    # `-WindowStyle Hidden` keeps the hundreds of per-test console windows from
    # flashing up while the corpus runs.
    $p = Start-Process -FilePath "cmd.exe" -ArgumentList "/c", "`"$batchFile`"" -PassThru -WindowStyle Hidden
    $finished = $p.WaitForExit($timeoutMs)
    if (-not $finished) {
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
    return @{
      code = $code
      timeout = $false
      stdout = ($so -replace "`r`n", "`n")
      stderr = ($se -replace "`r`n", "`n")
    }
  }

  # Reads a file a killed child process may still be holding. When a test hits
  # the timeout, the `cmd.exe` wrapper is killed but `node` keeps running for a
  # moment and still owns the redirect files, which made the read fail with
  # "The process cannot access the file" and turned a timeout into an internal
  # error of the harness. Retry briefly; an unreadable file reads as empty.
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

  # The severity/line/message triples of our own diagnostics.
  function Get-Diagnostics($text) {
    $diags = @()
    foreach ($line in ($text -split "`n")) {
      if ($line -match '^(error|warning|info):(.*?):(\d+):(\d+): (.*)$') {
        $diags += @{
          severity = $Matches[1]
          file = $Matches[2]
          line = [int]$Matches[3]
          text = $Matches[5]
        }
      }
    }
    return ,$diags
  }

  # The `.check` files are plain text: upstream writes them with
  # `removeAnsiColors` ("We remove ansi colors to make check files
  # human-readable"), so the ANSI SGR escapes the standard library's `Formatted`
  # output contains have to be dropped before comparing, too.
  function Remove-AnsiColors([string]$text) {
    return [regex]::Replace($text, "\u001b\[[;\d]*m", "")
  }

  # The expected diagnostics of a negative test: from the `.check` file when
  # there is one, otherwise from the `// ERROR` / `// WARN` comments.
  function Get-Expected($file) {
    $expected = @()
    $check = [IO.Path]::ChangeExtension($file, ".check")
    if (Test-Path $check) {
      foreach ($line in (Get-Content $check)) {
        if ($line -match '^\[(error|warning|info)\]\s+\S+?:(\d+):(\d+):\s*(.*)$') {
          $expected += @{ severity = $Matches[1]; line = [int]$Matches[2]; text = $Matches[4].Trim() }
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
    $jsOut = Join-Path $outDir (($rel -replace '[\\/]', '__') + ".js")

    if ($kind -eq "pos") {
      $check = [IO.Path]::ChangeExtension($file, ".check")
      $expected = ""
      if (Test-Path $check) {
        $expected = ([IO.File]::ReadAllText($check)).Replace("`r`n", "`n").TrimEnd()
      }
      $r = Invoke-Effekt $file $jsOut $true $rel
      if ($r.timeout) {
        "$kind`tfail`t$rel`ttimeout (30s)"
      } elseif ($r.code -ne 0) {
        $first = ($r.stderr -split "`n" | Where-Object { $_ -match '^(error|warning|info):' } | Select-Object -First 1)
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
      } elseif ((Remove-AnsiColors $r.stdout).TrimEnd() -ne $expected) {
        "$kind`tfail`t$rel`toutput differs"
      } else {
        "$kind`tok`t$rel`t"
      }
    } else {
      $expected = Get-Expected $file
      $r = Invoke-Effekt $file $jsOut $false $rel
      if ($r.timeout) {
        "$kind`tfail`t$rel`ttimeout (30s)"
        continue
      }
      $diags = Get-Diagnostics $r.stderr
      $missing = @()
      $wording = 0
      foreach ($e in $expected) {
        $match = $diags | Where-Object {
          $_.severity -eq $e.severity -and $_.line -eq $e.line
        } | Select-Object -First 1
        if (-not $match) {
          $missing += "$($e.severity) at line $($e.line)"
        } elseif ($e.text -ne "" -and -not ($match.text.Contains($e.text))) {
          $wording++
        }
      }
      if ($missing.Count -gt 0) {
        "$kind`tfail`t$rel`tmissing: $($missing -join ', ')"
      } elseif ($expected.Count -eq 0 -and $r.code -eq 0) {
        "$kind`tfail`t$rel`tcompiled without an error"
      } elseif ($wording -gt 0) {
        "$kind`twording`t$rel`t$wording message(s) differ in wording"
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
$tests = @()
foreach ($dir in @("pos", "stdlib")) {
  $base = Join-Path $corpus "examples/$dir"
  foreach ($f in (Get-ChildItem -Recurse $base -Filter '*.effekt' -File)) {
    $rel = $f.FullName.Substring($corpus.Length).TrimStart('\', '/') -replace '\\', '/'
    if ($Filter -ne "" -and -not $rel.Contains($Filter)) { continue }
    $tests += @{ kind = "pos"; file = $f.FullName; rel = $rel }
  }
}
$base = Join-Path $corpus "examples/neg"
foreach ($f in (Get-ChildItem -Recurse $base -Filter '*.effekt' -File)) {
  $rel = $f.FullName.Substring($corpus.Length).TrimStart('\', '/') -replace '\\', '/'
  if ($Filter -ne "" -and -not $rel.Contains($Filter)) { continue }
  $tests += @{ kind = "neg"; file = $f.FullName; rel = $rel }
}

$chunks = @()
for ($i = 0; $i -lt $jobs; $i++) { $chunks += ,@() }
for ($i = 0; $i -lt $tests.Count; $i++) { $chunks[$i % $jobs] += $tests[$i] }

$start = Get-Date
$jobObjects = @()
foreach ($chunk in $chunks) {
  if ($chunk.Count -eq 0) { continue }
  $jobObjects += Start-Job -ScriptBlock $worker -ArgumentList $cli, $libDir, $corpus, $outDir, $chunk
}
$results = $jobObjects | Wait-Job | Receive-Job
$jobObjects | Remove-Job
Write-Host ("compiled {0} test files in {1:N0}s" -f $tests.Count, ((Get-Date) - $start).TotalSeconds) -ForegroundColor DarkGray

# ---------------------------------------------------------------------------
# Summarize.
# ---------------------------------------------------------------------------
$posOk = 0
$posTotal = 0
$negOk = 0
$negTotal = 0
$negWording = 0
$failures = @{}

foreach ($line in $results) {
  if ($null -eq $line -or "$line" -eq "") { continue }
  $parts = "$line".Split("`t")
  if ($parts.Count -lt 4) { continue }
  $kind = $parts[0]
  $status = $parts[1]
  $rel = $parts[2]
  $detail = if ($parts.Count -gt 3) { $parts[3] } else { "" }
  if ($kind -eq "pos") {
    $posTotal++
    if ($status -eq "ok") { $posOk++ } else {
      if (-not $failures.ContainsKey($detail)) { $failures[$detail] = @() }
      $failures[$detail] += $rel
    }
  } else {
    $negTotal++
    if ($status -eq "ok") { $negOk++ }
    elseif ($status -eq "wording") { $negOk++; $negWording++ }
    else {
      if (-not $failures.ContainsKey($detail)) { $failures[$detail] = @() }
      $failures[$detail] += $rel
    }
  }
}

Write-Host ""
Write-Host ("positive (pos + stdlib): {0} of {1} pass" -f $posOk, $posTotal) -ForegroundColor Cyan
Write-Host ("negative (neg):          {0} of {1} match ({2} pass with different wording)" -f $negOk, $negTotal, $negWording) -ForegroundColor Cyan

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
if ($posOk -lt $positiveBaseline) {
  Write-Host ("positive: {0} pass, below the baseline of {1}" -f $posOk, $positiveBaseline) -ForegroundColor Red
  $failed = $true
}
if ($negOk -lt $negativeBaseline) {
  Write-Host ("negative: {0} match, below the baseline of {1}" -f $negOk, $negativeBaseline) -ForegroundColor Red
  $failed = $true
}
if ($failed) { exit 1 }
Write-Host ("baselines: positive {0}, negative {1}" -f $positiveBaseline, $negativeBaseline) -ForegroundColor Green
