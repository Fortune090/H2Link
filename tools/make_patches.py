"""Makes patches/ for a release: python tools/make_patches.py ORIGINALS PATCHED

ORIGINALS: an untouched H2EK folder (or a copy of just the files below, same relative paths).
PATCHED:   the same files as H2Link changes them, plus the patched game exes h2link_30tick.exe and h2link_60tick.exe
           (fixed names, so the Windows firewall rule survives updates; the build number is the exe's JIPv<N> tag).
Writes patches/*.h2p and patches/patches.json. Only differences are stored, never the H2EK files themselves.
"""
import glob, json, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src"))
import h2link

EXE_FROM = "halo2_tag_test.exe"            # the H2EK Tag Test the game exes are made from
TAGS = [
    "tags/ui/screens/game_shell/pregame_lobby/pregame_lobby.user_interface_screen_widget_definition",
    "tags/ui/ui_shared_globals.user_interface_shared_globals_definition",
    "tags/ui/player_skins/player_skin_lobby.user_interface_list_skin_definition",
    "tags/ui/screens/singleplayer/dialog_pause/dialog_pause.user_interface_screen_widget_definition",
    "tags/ui/screens/game_shell/settings_screen/player_profile/choose_primary_color.user_interface_screen_widget_definition",
    "tags/ui/screens/game_shell/settings_screen/player_profile/choose_player_model.user_interface_screen_widget_definition",
    "tags/ui/screens/game_shell/pregame_lobby/squad_settings.multilingual_unicode_string_list",
    "tags/ui/screens/game_shell/mp_game_select/mp_games.bitmap",
    "tags/ui/screens/game_shell/dialog_profile_select/dialog_profile.user_interface_screen_widget_definition",
    "tags/ui/screens/game_shell/main_menu_screen/main_menu_screen.multilingual_unicode_string_list",
    "tags/ui/screens/game_shell/online_y_menu/online_y_menu.user_interface_screen_widget_definition",
    "tags/globals/globals.globals",
    "debug_menu_init.txt",                      # the debug menu, trimmed for online play
]

def main(orig, patched):
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "patches")
    os.makedirs(out, exist_ok=True)
    for f in glob.glob(os.path.join(out, "*.h2p")):
        os.remove(f)
    items = []
    def add(file, frm, name, extra=None):
        src = open(os.path.join(orig, frm), "rb").read()
        dst = open(os.path.join(patched, file), "rb").read()
        p = h2link.patch_make(src, dst)
        assert h2link.patch_apply(p, src) == dst
        open(os.path.join(out, name), "wb").write(p)
        items.append(dict({"file": file.replace("\\", "/"), "from": frm.replace("\\", "/"), "patch": name}, **(extra or {})))
        print("%-60s %8d bytes" % (file, len(p)))
    exes = sorted(os.path.basename(p) for p in glob.glob(os.path.join(patched, "h2link_*tick.exe")))
    for e in exes:
        m = re.search(rb"JIPv(\d+)", open(os.path.join(patched, e), "rb").read())
        add(e, EXE_FROM, re.sub(r"\.exe$", ".h2p", e), {"version": int(m.group(1)) if m else 0})
    for t in TAGS:
        add(t, t, os.path.basename(t) + ".h2p")
    json.dump(items, open(os.path.join(out, "patches.json"), "w"), indent=1)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2])
