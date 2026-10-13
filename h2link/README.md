![H2L](assets/h2l_logo.png)

# H2Link

Online co-op for the Halo 2 Editing Kit's Tag Test (`halo2_tag_test.exe`): rooms on a lobby server, up to 16 players,
everyone's game started and joined together, join in progress, split-screen windows on one PC.

**Players:** download `H2Link_Setup.exe` from the [latest release](../../releases/latest) and run it. It asks
for the H2EK folder and makes H2Link's game files from the H2EK files already there: the game exes are made from
`halo2_tag_test.exe` (which stays as it is), and the tags and `debug_menu_init.txt` H2Link changes are kept in `h2link_backup` first. Uninstalling
puts the originals back. No H2EK files are part of this repository or its releases, only the differences.
H2Link checks this page for new releases and offers to install them. Everyone in a room should run the same
release.

**Without the installer:** `H2Link.exe --install-game "<H2EK folder>"` makes the game files,
`--check-game` only checks that the H2EK originals are there; `--restore-game` puts the originals back. An install changes all game files or, if an original is missing, none.

**Lobby server:** `H2Link.exe --server` (or `python src/h2link.py --server`), UDP 31100 open.

## Repository

| Folder | What |
|---|---|
| `src/h2link.py` | H2Link: launcher, tunnel, lobby server, control page |
| `patches/` | H2Link's changes to H2EK files (only the changed bytes, checked against the originals' SHA-256) |
| `tools/make_patches.py` | makes `patches/` from an untouched H2EK folder and the patched files |
| `installer/` | Inno Setup script, icon, server key, local build script |
| `.github/workflows/release.yml` | builds and publishes a release when a version tag is pushed |

See [RELEASING.md](RELEASING.md).
