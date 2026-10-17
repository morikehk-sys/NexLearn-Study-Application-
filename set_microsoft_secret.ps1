# Puts your Microsoft (Azure) client secret into .streamlit/secrets.toml.
#
# Run it from the project folder:   .\set_microsoft_secret.ps1
# It asks for the secret with hidden typing, so the secret never appears on
# screen or in any chat. Paste the secret's "Value" (Azure -> your app ->
# Certificates & secrets), not the "Secret ID".
param(
    [string]$Path = (Join-Path $PSScriptRoot ".streamlit\secrets.toml"),
    [string]$Secret  # optional, only for automated tests
)

if (-not (Test-Path -LiteralPath $Path)) { Write-Host "Can't find $Path"; exit 1 }

if (-not $Secret) {
    $secure = Read-Host "Paste your Microsoft client secret Value (typing is hidden)" -AsSecureString
    $ptr = [Runtime.InteropServices.Marshal]::SecureStringToBSTR($secure)
    try { $Secret = [Runtime.InteropServices.Marshal]::PtrToStringBSTR($ptr) }
    finally { [Runtime.InteropServices.Marshal]::ZeroFreeBSTR($ptr) }
}

$Secret = $Secret.Trim()
if ($Secret.Length -lt 8) { Write-Host "That looks too short to be a client secret. Nothing was changed."; exit 1 }
if ($Secret -match '^[0-9a-fA-F]{8}-([0-9a-fA-F]{4}-){3}[0-9a-fA-F]{12}$') {
    Write-Host "That looks like a Secret ID (a GUID), not the secret Value. Copy the 'Value' column instead. Nothing was changed."
    exit 1
}

$text = Get-Content -LiteralPath $Path -Raw -Encoding UTF8
$marker = "[auth.microsoft]"
$at = $text.IndexOf($marker)
if ($at -lt 0) { Write-Host "No [auth.microsoft] section in the file. Nothing was changed."; exit 1 }

$head = $text.Substring(0, $at)
$tail = $text.Substring($at)
$escaped = $Secret.Replace('\', '\\').Replace('"', '\"')
$new = [regex]::Replace($tail, '(?m)^client_secret\s*=\s*".*"\s*$', { param($m) 'client_secret = "' + $escaped + '"' }, 'None', [timespan]::FromSeconds(2))
if ($new -eq $tail) { Write-Host "Couldn't find the client_secret line to replace. Nothing was changed."; exit 1 }

[System.IO.File]::WriteAllText($Path, $head + $new, (New-Object System.Text.UTF8Encoding($false)))
Write-Host "Done. The Microsoft client secret is saved. Restart the Streamlit server to use it."
