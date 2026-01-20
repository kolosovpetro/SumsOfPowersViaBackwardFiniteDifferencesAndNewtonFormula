$InitialDirectory = Get-Location
cd $PSScriptRoot

$LatexFileName = (Get-ChildItem -Filter "*.tex" | Select-Object -First 1).BaseName
Write-Host "Latex file: $LatexFileName"  -ForegroundColor Magenta

pandoc "$LatexFileName.tex" --mathjax --standalone --citeproc `
    --bibliography="$LatexFileName.bib" `
    --csl=chicago-author-date.csl -o index.html

$EncodingScriptPath = "$InitialDirectory/scripts/Test-Encoding.ps1"

& $EncodingScriptPath -Autofix

Write-Host "Fix encoding is complete." -ForegroundColor Green
Write-Host "Exit Code: $LASTEXITCODE" -ForegroundColor Green
Write-Host "Changing Powershell Directory to $InitialDirectory ... " -ForegroundColor Green

cd $InitialDirectory