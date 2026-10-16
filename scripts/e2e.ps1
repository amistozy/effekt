# End-to-end test: compile each example with the MoonBit compiler and run the
# generated JavaScript with node, comparing against the expected output.
#
# Most cases run twice: once against the bundled Effekt standard library
# (`libraries/common/effekt.effekt`, the default) and once against
# `examples/minilib`, a stripped-down prelude that exercises a different path
# through the frontend. Cases that need a module minilib does not provide (for
# instance `import exception`) list the libraries they apply to explicitly.
#
# Usage: powershell -File scripts/e2e.ps1

$ErrorActionPreference = "Continue"
$root = Split-Path -Parent $PSScriptRoot
Push-Location $root

Write-Host "building the compiler..." -ForegroundColor Cyan
moon build --target js 2>&1 | Out-Null
if ($LASTEXITCODE -ne 0) { Pop-Location; exit 1 }

$cli = Join-Path $root "_build/js/debug/build/cmd/main/main.js"
$all = @("libraries", "examples/minilib")
$stdlib_only = @("libraries")

# example name -> @{ out = expected stdout; libs = libraries to run it against }
$cases = [ordered]@{
  "hello"                   = @{ out = "Hello, world!";          libs = $all }
  "fib"                     = @{ out = "6765";                   libs = $all }
  "match"                   = @{ out = "6";                      libs = $all }
  "higher_order"            = @{ out = "1`n2`n3`n4";             libs = $all }
  "mutable"                 = @{ out = "2";                      libs = $all }
  "while"                   = @{ out = "10";                     libs = $all }
  "amb"                     = @{ out = "66";                     libs = $all }
  "exception"               = @{ out = "division by zero`n-1";   libs = $all }
  "toplevel_val"            = @{ out = "1";                      libs = $all }
  "char"                    = @{ out = "A`nok";                  libs = $all }
  # `import exception` needs the real standard library.
  "import_handler"          = @{ out = "boom`n0";                libs = $stdlib_only }
  "import_handler_qualified" = @{ out = "boom`n0";               libs = $stdlib_only }
}

$failed = 0
$passed = 0
foreach ($lib in @("libraries", "examples/minilib")) {
  Write-Host "standard library: $lib" -ForegroundColor Cyan
  foreach ($name in $cases.Keys) {
    $case = $cases[$name]
    if ($case.libs -notcontains $lib) { continue }
    $expected = $case.out
    $actual = (& node $cli --lib $lib --run "examples/$name.effekt" 2>$null | Out-String) -replace "`r`n", "`n"
    $actual = $actual.Trim()
    if ($actual -eq $expected.Trim()) {
      Write-Host "  ok    $name" -ForegroundColor Green
      $passed++
    } else {
      Write-Host "  FAIL  $name" -ForegroundColor Red
      Write-Host "    expected: $($expected.Trim() -replace "`n", ' | ')"
      Write-Host "    actual:   $($actual -replace "`n", ' | ')"
      $failed++
    }
  }
}

Pop-Location
if ($failed -gt 0) {
  Write-Host "$failed of $($failed + $passed) end-to-end test(s) failed" -ForegroundColor Red
  exit 1
}
Write-Host "all $passed end-to-end tests passed" -ForegroundColor Green
