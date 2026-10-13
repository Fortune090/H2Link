# Making a release

1. Update what changed:
   - `src/h2link.py` for an H2Link change (its `VERSION` line is set from the tag by the build).
   - New game files: on your PC, keep an untouched copy of the H2EK files (`halo2_tag_test.exe` and the original tags)
     and the patched files, then run

         python tools/make_patches.py <untouched H2EK folder> <folder with the patched files>

     The patched folder holds `h2link_30tick.exe`, `h2link_60tick.exe` (fixed names; the build number is the exe's own `JIPv<N>` tag) and the changed tags at their
     `tags\...` paths. This rewrites `patches/`: only differences, never the H2EK files.
2. Commit and push.
3. Tag and push the tag:

       git tag v1.0.21
       git push origin v1.0.21

GitHub Actions builds `H2Link_Setup.exe` (with H2Link and its game-file patches inside) and publishes it with
`manifest.json` as the release `H2Link v<version>`. Within six hours every running H2Link shows
"An update is out" with an Install update button. The installer makes the new game files from each player's
own H2EK files (or from the originals kept in `h2link_backup`, for files an earlier release changed).

Local build without GitHub: `installer\build.bat 1.0.30 <owner>/<repository>` (needs Python 3 and Inno Setup 6).

The update check asks `https://api.github.com/repos/<this repository>/releases/latest`, so the repository
must be public for players' copies to see releases.

A letter after the numbers is a follow-up release: `v1.1.7a` counts as newer than `v1.1.7` and older than `v1.1.8`
(H2Link 1.1.7a and later read it that way; 1.1.7 and earlier ignore the letter, so they are not offered a letter release).

Test build without publishing: Actions > Test build > Run workflow on any branch. It makes `H2Link.exe` and
`H2Link_Setup.exe` as the run's artifact; no release, so no player's update check sees it.
