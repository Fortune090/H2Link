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
; H2Link.exe is compressed already: a light setting unpacks fastest (quick silent updates)
Compression=lzma2/fast
SolidCompression=no
WizardStyle=modern
CloseApplications=yes

[Tasks]
Name: "desktopicon"; Description: "Create a desktop shortcut"; GroupDescription: "Shortcuts:"

[Files]
Source: "dist\H2Link.exe"; DestDir: "{app}"; Flags: ignoreversion
; The release's lobby server key - unless this install uses its own lobby server (server_custom.flag next to
; H2Link.exe): then server.key was made from that address at install and updates never replace it.
Source: "installer\server.key"; DestDir: "{app}"; Flags: ignoreversion; Check: UseReleaseKey
; Microsoft's WebView2 runtime, which draws H2Link's window: part of Windows 11, missing on some Windows 10 PCs.
; The build downloads Microsoft's small bootstrapper; it is only run when the runtime is not there.
Source: "build\MicrosoftEdgeWebview2Setup.exe"; DestDir: "{tmp}"; Flags: deleteafterinstall; Check: NeedsWebView2

[Icons]
Name: "{autoprograms}\H2Link"; Filename: "{app}\H2Link.exe"; WorkingDir: "{app}"
Name: "{autodesktop}\H2Link"; Filename: "{app}\H2Link.exe"; WorkingDir: "{app}"; Tasks: desktopicon

[Run]
Filename: "{tmp}\MicrosoftEdgeWebview2Setup.exe"; Parameters: "/silent /install"; StatusMsg: "Installing Microsoft WebView2 (draws H2Link's window)..."; Flags: waituntilterminated; Check: NeedsWebView2
Filename: "{app}\H2Link.exe"; WorkingDir: "{app}"; Description: "Start H2Link now"; Flags: postinstall nowait skipifsilent

[UninstallDelete]
Type: filesandordirs; Name: "{app}\reports"
Type: files; Name: "{app}\h2link.json"
Type: files; Name: "{app}\gamedir.txt"
Type: files; Name: "{app}\server_custom.flag"
Type: files; Name: "{app}\server.key"
Type: files; Name: "{app}\game_files.log"

[Code]
const
  WV2 = '{F3017226-FE2A-4295-8BDF-00C3A9A7E4C5}';

function WebView2At(Root: Integer; Key, Folder: String): Boolean;
{ registered AND its files really there: a registry entry left behind by a removed or damaged runtime does
  not count (H2Link's window then reports "Couldn't find a compatible Webview2 Runtime installation") }
var
  V: String;
begin
  Result := RegQueryStringValue(Root, Key, 'pv', V) and (V <> '') and (V <> '0.0.0.0') and
            FileExists(AddBackslash(Folder) + V + '\msedgewebview2.exe');
end;

function NeedsWebView2: Boolean;
begin
  Result := not (WebView2At(HKLM, 'SOFTWARE\WOW6432Node\Microsoft\EdgeUpdate\Clients\' + WV2,
                            ExpandConstant('{commonpf32}\Microsoft\EdgeWebView\Application')) or
                 WebView2At(HKLM, 'SOFTWARE\Microsoft\EdgeUpdate\Clients\' + WV2,
                            ExpandConstant('{commonpf32}\Microsoft\EdgeWebView\Application')) or
                 WebView2At(HKCU, 'Software\Microsoft\EdgeUpdate\Clients\' + WV2,
                            ExpandConstant('{localappdata}\Microsoft\EdgeWebView\Application')));
end;

var
  GamePage: TInputDirWizardPage;
  ServerPage: TWizardPage;
  OwnServer: TNewCheckBox;
  ServerAddr: TNewEdit;

function CustomFlag: String;
begin
  Result := ExpandConstant('{app}\server_custom.flag');
end;

{ The release's server.key is installed unless this install uses its own lobby server: chosen now, or chosen
  in an earlier install (the flag file) - so a silent update never replaces a key made for this PC. }
function UseReleaseKey: Boolean;
begin
  if WizardSilent then
    Result := not FileExists(CustomFlag)
  else
    Result := not OwnServer.Checked;
end;

procedure OwnServerClick(Sender: TObject);
begin
  ServerAddr.Enabled := OwnServer.Checked;
end;

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

  ServerPage := CreateCustomPage(GamePage.ID, 'Lobby server', 'Which lobby server should H2Link use?');
  OwnServer := TNewCheckBox.Create(ServerPage);
  OwnServer.Parent := ServerPage.Surface;
  OwnServer.Width := ServerPage.SurfaceWidth;
  OwnServer.Caption := 'Use my own lobby server (instead of the one this release comes with)';
  OwnServer.OnClick := @OwnServerClick;
  with TNewStaticText.Create(ServerPage) do begin
    Parent := ServerPage.Surface;
    Top := OwnServer.Top + OwnServer.Height + ScaleY(10);
    Caption := 'IP address or host name, with :port only if it is not 31100:';
  end;
  ServerAddr := TNewEdit.Create(ServerPage);
  ServerAddr.Parent := ServerPage.Surface;
  ServerAddr.Top := OwnServer.Top + OwnServer.Height + ScaleY(30);
  ServerAddr.Width := ScaleX(260);
  ServerAddr.Text := GetPreviousData('ServerAddr', '');
  OwnServer.Checked := (GetPreviousData('OwnServer', '0') = '1') or FileExists(ExpandConstant('{localappdata}\Programs\H2Link\server_custom.flag'));
  ServerAddr.Enabled := OwnServer.Checked;
  with TNewStaticText.Create(ServerPage) do begin
    Parent := ServerPage.Surface;
    Top := ServerAddr.Top + ServerAddr.Height + ScaleY(12);
    Width := ServerPage.SurfaceWidth;
    AutoSize := False;
    Height := ScaleY(60);
    WordWrap := True;
    Caption := 'H2Link makes a server key from this address for this install. Updates keep it: they never replace ' +
               'it with the release''s key. Run this installer again and untick the box to go back to the release''s server.';
  end;
end;

procedure RegisterPreviousData(PreviousDataKey: Integer);
begin
  SetPreviousData(PreviousDataKey, 'GameDir', GamePage.Values[0]);
  if OwnServer.Checked then
    SetPreviousData(PreviousDataKey, 'OwnServer', '1')
  else
    SetPreviousData(PreviousDataKey, 'OwnServer', '0');
  SetPreviousData(PreviousDataKey, 'ServerAddr', ServerAddr.Text);
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
  if not Exec(ExpandConstant('{tmp}\H2Link.exe'), '--check-game "' + Dir + '" --log "' + Log + '"', '',
              SW_HIDE, ewWaitUntilTerminated, Code) then begin
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
  if (CurPageID = ServerPage.ID) and OwnServer.Checked and (Trim(ServerAddr.Text) = '') then begin
    MsgBox('Enter your lobby server''s IP address or host name, or untick the box.', mbError, MB_OK);
    Result := False;
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
  if (CurStep = ssPostInstall) and not WizardSilent then begin
    if OwnServer.Checked then begin
      if Exec(ExpandConstant('{app}\H2Link.exe'), '--make-key "' + Trim(ServerAddr.Text) + '" --key-out "' +
              ExpandConstant('{app}\server.key') + '"', '', SW_HIDE, ewWaitUntilTerminated, Code) and (Code = 0) then
        SaveStringToFile(CustomFlag, Trim(ServerAddr.Text), False)
      else
        MsgBox('"' + Trim(ServerAddr.Text) + '" is not a usable lobby server address, so H2Link uses the release''s ' +
               'server for now. Run this installer again to enter it.', mbError, MB_OK);
    end else
      DeleteFile(CustomFlag);
  end;
  if CurStep = ssPostInstall then begin
    SaveStringToFile(ExpandConstant('{app}\gamedir.txt'), GamePage.Values[0], False);
    Cfg := ExpandConstant('{app}\h2link.json');
    if not FileExists(Cfg) then
      SaveStringToFile(Cfg, '{"game_dir": "' + JsonPath(GamePage.Values[0]) + '"}', False);
    { the game files, made from this player's own H2EK files }
    Log := ExpandConstant('{app}\game_files.log');
    WizardForm.StatusLabel.Caption := 'Making the game files from your H2EK files...';
    if not Exec(ExpandConstant('{app}\H2Link.exe'), '--install-game "' + GamePage.Values[0] + '" --log "' + Log + '"',
                '', SW_HIDE, ewWaitUntilTerminated, Code) or (Code <> 0) then
      MsgBox('Some H2EK files were left as they are, because they are not the H2EK''s original files ' +
             '(changed earlier by hand or by an older H2Link copy).' + #13#10 + #13#10 +
             'To fix this: in Steam, Library > H2EK > Properties > Installed Files > Verify integrity of tool ' +
             'files. Then run this installer again.' + #13#10 + #13#10 + 'Details: ' + Log, mbError, MB_OK);
    { an update started from H2Link runs without any window: H2Link starts again once the game files are done }
    if WizardSilent then
      Exec(ExpandConstant('{app}\H2Link.exe'), '', ExpandConstant('{app}'), SW_SHOWNORMAL, ewNoWait, Code);
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
