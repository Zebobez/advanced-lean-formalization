$ErrorActionPreference = "Stop"

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$sourceRoot = [System.IO.Path]::GetFullPath((Join-Path $repoRoot "manuscript"))
$summaryPath = Join-Path $sourceRoot "SUMMARY.md"
$defaultsPath = Join-Path $PSScriptRoot "kindle.defaults.yaml"

$pandocCommand = Get-Command pandoc -ErrorAction Stop
$inputFiles = [System.Collections.Generic.List[string]]::new()
$sourcePrefix = $sourceRoot.TrimEnd([char[]]@("\", "/")) + [System.IO.Path]::DirectorySeparatorChar

foreach ($line in Get-Content -LiteralPath $summaryPath) {
    if ($line -notmatch '^\s*(?:-\s*)?\[[^\]]+\]\(([^)]+)\)\s*$') {
        continue
    }

    $relativePath = $Matches[1]
    if ($relativePath -match '^(?:[a-z][a-z0-9+.-]*:|#)') {
        continue
    }
    if ($relativePath -notmatch '\.md(?:#.*)?$') {
        continue
    }

    $relativePath = $relativePath -replace '#.*$', ''
    $relativePath = $relativePath.Replace('/', [System.IO.Path]::DirectorySeparatorChar)
    $fullPath = [System.IO.Path]::GetFullPath((Join-Path $sourceRoot $relativePath))
    if (-not $fullPath.StartsWith($sourcePrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "Summary entry escapes the source directory: $relativePath"
    }
    if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) {
        throw "Summary entry does not exist: $relativePath"
    }

    $inputFiles.Add($fullPath)
}

if ($inputFiles.Count -eq 0) {
    throw "No Markdown chapters were found in $summaryPath"
}

$outputDirectory = Join-Path $repoRoot "build\kindle"
New-Item -ItemType Directory -Force -Path $outputDirectory | Out-Null
$outputPath = Join-Path $outputDirectory "Advanced-Lean-for-Mathematics.epub"

$pandocArgs = @(
    "--defaults", $defaultsPath,
    "--mathml",
    "--resource-path", $sourceRoot,
    "--output", $outputPath
) + $inputFiles.ToArray()

& $pandocCommand.Source @pandocArgs
if ($LASTEXITCODE -ne 0) {
    throw "Pandoc failed with exit code $LASTEXITCODE"
}

Write-Output "Created $outputPath"
