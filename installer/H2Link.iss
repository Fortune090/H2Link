; H2Link installer (Inno Setup 6). The release workflow (or installer\build.bat) builds dist\H2Link.exe, which
; carries the game-file patches, and compiles this with /DAppVer=<H2Link version> into Output\H2Link_Setup.exe.
;   H2Link.exe and server.key  -> %LOCALAPPDATA%\Programs\H2Link (no administrator rights)
;   game files                 -> made by "H2Link.exe --install-game" from the player's own H2EK files: new game
;                                 exes next to halo2_tag_test.exe, changed tags with their originals kept in h2link_backup
; Uninstalling runs "H2Link.exe --restore-game": the originals go back, H2Link's game exes are removed.

#ifndef AppVer
  #define AppVer "0.0.0"
#endif

[Setup]
AppId={{6F3D2C1A-8E4B-4B7A-9C2D-4A1B2C3D4E5F}
AppName=H2Link
AppVersion={#AppVer}
AppPublisher=H2Link
SourceDir=..
DefaultDirName={localappdata}\Programs\H2Link
DisableProgramGroupPage=yes
PrivilegesRequired=lowest
OutputDir=Output
OutputBaseFilename=H2Link_Setup
SetupIconFile=installer\h2link.ico
UninstallDisplayIcon={app}\H2Link.exe
Compression=lzma2/max
SolidCompression=yes
WizardStyle=modern
CloseApplications=yes

[Tasks]
Name: "desktopicon"; Description: "Create a desktop shortcut"; GroupDescription: "Shortcuts:"

[Files]
Source: "dist\H2Link.exe"; DestDir: "{app}"; Flags: ignoreversion
Source: "installer\server.key"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{autoprograms}\H2Link"; Filename: "{app}\H2Link.exe"; WorkingDir: "{app}"
Name: "{autodesktop}\H2Link"; Filename: "{app}\H2Link.exe"; WorkingDir: "{app}"; Tasks: desktopicon

[Run]
Filename: "{app}\H2Link.exe"; WorkingDir: "{app}"; Description: "Start H2Link now"; Flags: postinstall nowait skipifsilent

[UninstallDelete]
Type: filesandordirs; Name: "{app}\reports"
Type: files; Name: "{app}\h2link.json"
Type: files; Name: "{app}\gamedir.txt"
Type: files; Name: "{app}\game_files.log"

[Code]
var
  GamePage: TInputDirWizardPage;

function SteamH2EK: String;
var
  P: String;
begin
  Result := '';
  if RegQueryStringValue(HKCU, 'Software\Valve\Steam', 'SteamPath', P) then begin
    StringChangeEx(P, '/', '\', True);
    if DirExists(P + '\steamapps\common\H2EK') then
      Result := P + '\steamapps\common\H2EK';
  end;
  if (Result = '') and DirExists(ExpandConstant('{commonpf32}') + '\Steam\steamapps\common\H2EK') then
    Result := ExpandConstant('{commonpf32}') + '\Steam\steamapps\common\H2EK';
end;

procedure InitializeWizard;
begin
  GamePage := CreateInputDirPage(wpSelectDir, 'Game folder',
    'Where is the Halo 2 Editing Kit (H2EK)?',
    'H2Link makes its game files from the H2EK files in this folder. The files it changes are kept in ' +
    'h2link_backup and put back when H2Link is uninstalled.', False, '');
  GamePage.Add('');
  GamePage.Values[0] := GetPreviousData('GameDir', SteamH2EK);
end;

procedure RegisterPreviousData(PreviousDataKey: Integer);
begin
  SetPreviousData(PreviousDataKey, 'GameDir', GamePage.Values[0]);
end;

function CheckGameFiles(Dir: String): Boolean;
{ Before anything is installed: every H2EK original H2Link's game files are made from must be there.
  If one is not, setup does not go on - nothing is changed in the game folder. }
var
  Code: Integer;
  Log: String;
  Text: AnsiString;
begin
  Result := False;
  ExtractTemporaryFile('H2Link.exe');
  Log := ExpandConstant('{tmp}\check.log');
  if not Exec(ExpandConstant('{cmd}'), '/C ""' + ExpandConstant('{tmp}\H2Link.exe') + '" --check-game "' + Dir +
              '" > "' + Log + '" 2>&1"', '', SW_HIDE, ewWaitUntilTerminated, Code) then begin
    MsgBox('The game folder could not be checked.', mbError, MB_OK);
    exit;
  end;
  if Code = 0 then begin
    Result := True;
    exit;
  end;
  if not LoadStringFromFile(Log, Text) then
    Text := '';
  MsgBox('H2Link cannot be installed into this H2EK folder yet: some of its files are not the H2EK''s ' +
         'original files (changed earlier by hand or by an older H2Link copy).' + #13#10 + #13#10 +
         'In Steam: Library > H2EK > Properties > Installed Files > Verify integrity of tool files. Then run ' +
         'this installer again.' + #13#10 + #13#10 + Trim(String(Text)), mbError, MB_OK);
end;

function NextButtonClick(CurPageID: Integer): Boolean;
begin
  Result := True;
  if CurPageID = GamePage.ID then begin
    if not FileExists(AddBackslash(GamePage.Values[0]) + 'halo2_tag_test.exe') then begin
      MsgBox('This folder has no halo2_tag_test.exe, so it is not the H2EK folder.', mbError, MB_OK);
      Result := False;
    end else
      Result := CheckGameFiles(GamePage.Values[0]);
  end;
end;

function JsonPath(S: String): String;
begin
  Result := S;
  StringChangeEx(Result, '\', '\\', True);
  StringChangeEx(Result, '"', '\"', True);
end;

procedure CurStepChanged(CurStep: TSetupStep);
var
  Code: Integer;
  Cfg, Log: String;
begin
  if CurStep = ssPostInstall then begin
    SaveStringToFile(ExpandConstant('{app}\gamedir.txt'), GamePage.Values[0], False);
    Cfg := ExpandConstant('{app}\h2link.json');
    if not FileExists(Cfg) then
      SaveStringToFile(Cfg, '{"game_dir": "' + JsonPath(GamePage.Values[0]) + '"}', False);
    { the game files, made from this player's own H2EK files }
    Log := ExpandConstant('{app}\game_files.log');
    WizardForm.StatusLabel.Caption := 'Making the game files from your H2EK files...';
    if not Exec(ExpandConstant('{cmd}'), '/C ""' + ExpandConstant('{app}\H2Link.exe') + '" --install-game "' +
                GamePage.Values[0] + '" > "' + Log + '" 2>&1"', '', SW_HIDE, ewWaitUntilTerminated, Code) or (Code <> 0) then
      MsgBox('Some H2EK files were left as they are, because they are not the H2EK''s original files ' +
             '(changed earlier by hand or by an older H2Link copy).' + #13#10 + #13#10 +
             'To fix this: in Steam, Library > H2EK > Properties > Installed Files > Verify integrity of tool ' +
             'files. Then run this installer again.' + #13#10 + #13#10 + 'Details: ' + Log, mbError, MB_OK);
  end;
end;

procedure CurUninstallStepChanged(CurUninstallStep: TUninstallStep);
var
  Code: Integer;
  G: AnsiString;
begin
  if CurUninstallStep = usUninstall then begin
    { before H2Link.exe is removed: the H2EK originals go back }
    if LoadStringFromFile(ExpandConstant('{app}\gamedir.txt'), G) then
      Exec(ExpandConstant('{app}\H2Link.exe'), '--restore-game "' + Trim(G) + '"', '', SW_HIDE, ewWaitUntilTerminated, Code);
  end;
end;
