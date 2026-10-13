@echo off
rem Local build of H2Link.exe and H2Link_Setup.exe - the same steps as .github\workflows\release.yml.
rem   installer\build.bat <version> [<github owner/repository>]      e.g.  installer\build.bat 1.0.30 Fortune/h2link
rem Needs Python 3 (python.org) and Inno Setup 6 (jrsoftware.org). Output: Output\H2Link_Setup.exe and manifest.json
rem (upload both to a GitHub release named v<version> for the update check; dist\H2Link.exe is only built for the installer).
setlocal
cd /d "%~dp0\.."
if "%~1"=="" (echo usage: installer\build.bat ^<version^> [^<owner/repository^>] & exit /b 1)
set "VER=%~1"
set "REPO=%~2"
if not exist build mkdir build
rem this build's version and update repository, stamped into a copy of the source
powershell -NoProfile -Command "$s = Get-Content src\h2link.py -Raw; $s = $s -replace 'VERSION = \"[^\"]*\"', ('VERSION = \"' + $env:VER + '\"'); if ($env:REPO) { $s = $s -replace '__H2LINK_REPO__', $env:REPO }; Set-Content build\h2link.py $s -NoNewline -Encoding UTF8" || goto failed
py -3 -m pip install --upgrade pyinstaller pywebview || goto failed
py -3 -m PyInstaller --noconfirm --onefile --windowed --name H2Link --icon "%CD%\installer\h2link.ico" --add-data "%CD%\patches;patches" --distpath dist --workpath build\work --specpath build build\h2link.py || goto failed
set "ISCC=%ProgramFiles(x86)%\Inno Setup 6\ISCC.exe"
if not exist "%ISCC%" set "ISCC=%LOCALAPPDATA%\Programs\Inno Setup 6\ISCC.exe"
if not exist "%ISCC%" (echo Inno Setup 6 not found - dist\H2Link.exe is built, the installer is not. & goto manifest)
if not exist build\MicrosoftEdgeWebview2Setup.exe powershell -NoProfile -Command "Invoke-WebRequest 'https://go.microsoft.com/fwlink/p/?LinkId=2124703' -OutFile build\MicrosoftEdgeWebview2Setup.exe" || goto failed
"%ISCC%" /DAppVer=%VER% installer\H2Link.iss || goto failed
:manifest
powershell -NoProfile -Command "$p = Get-Content patches\patches.json -Raw | ConvertFrom-Json; $e = ($p | Where-Object { $_.file -match '_v(\d+)_30tick' } | ForEach-Object { [regex]::Match($_.file, '_v(\d+)_').Groups[1].Value } | Select-Object -First 1); if (-not $e) { $e = 0 }; Set-Content manifest.json ('{\"h2link\": \"' + $env:VER + '\", \"exe\": ' + $e + ', \"installer\": \"H2Link_Setup.exe\"}') -NoNewline"
echo.
echo Done: Output\H2Link_Setup.exe and manifest.json
pause
exit /b 0
:failed
echo.
echo The build stopped with an error - see the lines above.
pause
exit /b 1
