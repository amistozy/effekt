# Regression gate for the Effekt standard library.
#
# The port's own tests (`moon test`) and `scripts/e2e.ps1` cover the language
# with a few small programs; the standard library is a much larger corpus, and
# every phase bug shows up there first (`stream::zip` went unnoticed until it
# was compiled, and it blocked half of the library). This script compiles every
# module under `libraries/` and counts how many of them get through.
#
# A module "compiles" when it either produces JavaScript or stops only because
# it has no `main` — library modules have none, and that error is reported by
# code generation, after every phase has run. The baseline can only grow: lower
# it only when a module is removed from `libraries/`.
#
# Usage: powershell -File scripts/stdlib.ps1

$ErrorActionPreference = "Continue"
$root = Split-Path -Parent $PSScriptRoot
Push-Location $root

Write-Host "building the compiler..." -ForegroundColor Cyan
moon build --target js 2>&1 | Out-Null
if ($LASTEXITCODE -ne 0) { Pop-Location; exit 1 }

$cli = Join-Path $root "_build/js/debug/build/cmd/main/main.js"
$baseline = 15

$ok = 0
$failures = @{}
$total = 0
foreach ($file in (Get-ChildItem libraries -Recurse -Filter *.effekt)) {
  $rel = $file.FullName.Replace("$root\", "").Replace("\", "/")
  $total++
  $stdout = [System.IO.Path]::GetTempFileName()
  $stderr = [System.IO.Path]::GetTempFileName()
  $proc = Start-Process -FilePath node -ArgumentList @($cli, "--show-js", $rel) `
    -NoNewWindow -Wait -PassThru `
    -RedirectStandardOutput $stdout -RedirectStandardError $stderr
  $message = (Get-Content $stderr -Raw)
  Remove-Item $stdout, $stderr -Force
  if ($null -eq $message) { $message = "" }

  if ($proc.ExitCode -eq 0 -or $message -match "Cannot find the entry point") {
    $ok++
    Write-Host "  ok    $rel" -ForegroundColor Green
  } else {
    $first = ($message -split "`n" | Where-Object { $_ -match '\S' } | Select-Object -First 1)
    # Drop the leading `error:` and any `file:line:col:` prefix, so that the
    # same bug in different modules groups together.
    $first = ($first -replace '^error:\s*', '') -replace '^.*?\.effekt:\d+:\d+:\s*', ''
    if (-not $failures.ContainsKey($first)) { $failures[$first] = @() }
    $failures[$first] += $rel
    Write-Host "  FAIL  $rel" -ForegroundColor DarkYellow
  }
}

Pop-Location
Write-Host ""
if ($failures.Count -gt 0) {
  Write-Host "remaining failures:" -ForegroundColor Cyan
  foreach ($message in ($failures.Keys | Sort-Object { -$failures[$_].Count })) {
    $files = $failures[$message]
    Write-Host ("  {0,3}  {1}" -f $files.Count, $message)
    if ($files.Count -le 3) {
      foreach ($f in $files) { Write-Host "         $f" -ForegroundColor DarkGray }
    }
  }
  Write-Host ""
}
if ($ok -lt $baseline) {
  Write-Host "$ok of $total standard library modules compile, below the baseline of $baseline" -ForegroundColor Red
  exit 1
}
Write-Host "$ok of $total standard library modules compile (baseline $baseline)" -ForegroundColor Green
