![H2L](assets/h2link_logo.png)

## CONNECTION QUALITY NOT GUARANTEED. INITIAL PUBLIC RELEASE.

Up to 16-Player online co-op for the Halo 2 Editing Kit's Tag Test (`halo2_tag_test.exe`). Up to 4 players split-screen on each PC. Full Server/Room browser. Join in progress fully functional. H2EK's debug menu and cheats also working for all players. Have fun!

**NOTE:** MCC/H2EK Required. If you do not have H2EK installed, you can find it on MCC's DLC page as "HALO 2 MOD TOOLS - MCC". Install via Steam. For best gameplay experience, install to an SSD, if possible. Open H2EK directory (in steamapps\common) and run "H2EK (Extract).bat". Wait for this to complete before running the H2Link installer.

Download `H2Link_Setup.exe` from the [latest release](../../releases/latest) and run it. It asks for the H2EK folder and creates/patches H2Link's game files automatically if they are detected.  Uninstalling reverts all files to their original state. No H2EK files are part of this repository, all files are backed up and patched in place.

H2Link checks for updates at launch. Everyone in a room should be running the same version.

**Lobby server:** I am hosting one myself, but you can run one yourself if you wish. `H2Link.exe --server` from a Command Prompt (its output appears there), or `python src/h2link.py --server`; ensure UDP 31100 is open and that it is properly forwarded on your router.

## Repository

| Folder | What |
|---|---|
| `src/h2link.py` | H2Link: launcher, tunnel, lobby server, control page |
| `patches/` | H2Link's changes to H2EK files (only the changed bytes, checked against the originals' SHA-256) |
| `tools/make_patches.py` | makes `patches/` from an untouched H2EK folder and the patched files |
| `installer/` | Inno Setup script, icon, server key, local build script |
| `.github/workflows/release.yml` | builds and publishes a release when a version tag is pushed |

See [RELEASING.md](RELEASING.md).
