#!/usr/bin/env python3
"""
H2Link - carries the system link of the Halo 2 Tag Test "sysnet auto16" builds
between PCs over the internet.

How it fits the game (addresses from halo2_sysnet_auto16_v33/v34):
  * A game instance owns one "slot" (0-15). It listens on UDP 1000/1002/1005/1006
    + slot*110 and reaches every other slot on 127.0.0.1 at that slot's ports.
  * H2Link holds the named mutex of every slot that belongs to another PC, so the
    game takes a slot that is unique in the room and its discovery fan-out covers
    everyone, and it binds those slots' ports. A packet the game sends to a remote
    slot is forwarded to the PC that owns it and re-sent there from the sender's
    slot port, because the game identifies a sender by source port alone.
  * The shared page "h2ek_sysnet_cheatsync" (cheat flags, teleport and drop
    relays, join sync) is mirrored between PCs, and the join-in-progress save
    (core\\<name>.bin) is sent to every PC before its page shows the new sync.

Standard library only. Started by H2Link.bat, which brings its own private runtime.
"""
import argparse
import base64
import collections
import ctypes
import glob
import hashlib
import hmac
import json
import mmap
import os
import platform
import queue
import random
import re
import select
import selectors
import shlex
import socket
import struct
import subprocess
import sys
import shutil
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid as uuid_mod
import webbrowser
import zipfile
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

APP = "H2Link"
VERSION = "1.0.54"
# Where new releases are published (GitHub "owner/repository"). The release build fills this in; a
# setting "update_repo" in h2link.json overrides it. Each release carries manifest.json:
#   {"h2link": "1.0.20", "exe": 78, "installer": "H2Link_Setup.exe"}
UPDATE_REPO = "__H2LINK_REPO__"
UPDATE_EVERY = 6 * 3600.0
ISSUES_URL = "https://github.com/Fortune090/H2Link/issues/new"     # where players report problems
PROTO = 2
IS_WIN = os.name == "nt"

# ---- facts about the game build -------------------------------------------
MAX_WINDOWS = 4                     # game windows per PC: one controller each, and 4 controllers work per PC
NSLOTS = 16
SPACING = 110                           # port distance between slots (v31+)
BASE_PORTS = (1000, 1002, 1005, 1006)   # 1002 = discovery, joins, game data
PAGE_NAME = "h2ek_sysnet_cheatsync"
PAGE_SIZE = 0x1000
MUTEX_FMT = "h2ek_sysnet_slot%02d"
G_OFF, G_LEN = 0x000, 0x100             # global cheat flags, one byte each
P_OFF, P_LEN = 0x400, 0x10              # per-player cheat bits, OR of all players
EVENTS = {1: (0x100, 0x100),            # teleport relay: seq, sender, payload
          2: (0x200, 0x200)}            # object drop relay: seq, sender, payload
JS_SEQ, JS_SENDER, JS_NEXT, JS_COUNT, JS_NAME = 0x800, 0x804, 0x808, 0x80C, 0x810
# exe v39+: cheat commands. Each slot's game writes commands, stamped with the game tick at which they
# take effect, into its own lane; every PC must see every lane, so each PC's lanes are copied to the others.
LANE_OFF, LANE_LEN = 0x900, 0x40
# exe v70+: on the room host's PC only, how many game windows the room has, written at its launch. The host's
# game holds its first level until that many machines have asked to join (not mirrored to other PCs).
EXPECT_OFF = 0xF00
JS_FORCE = 0x1000                       # added to the loaded count to end a hold
def split_rects(n, x, y, w, h):
    """Screen areas for a PC's game windows, split-screen style: 1 = the whole area; 2 = left | right;
    3 = top, then bottom left | bottom right (on a 21:9 or wider area: left, then top right | bottom right);
    4 = the four quarters (top left, top right, bottom left, bottom right). Window k (0 = this PC's first) gets
    rects[k]."""
    hw, hh = w // 2, h // 2
    if n <= 1:
        return [(x, y, w, h)]
    if n == 2:
        return [(x, y, hw, h), (x + hw, y, w - hw, h)]
    if n == 3:
        if h > 0 and w / h >= 2.2:                     # 21:9 and wider (the area above the taskbar is a bit wider)
            return [(x, y, hw, h), (x + hw, y, w - hw, hh), (x + hw, y + hh, w - hw, h - hh)]
        return [(x, y, w, hh), (x, y + hh, hw, h - hh), (x + hw, y + hh, w - hw, h - hh)]
    return [(x, y, hw, hh), (x + hw, y, w - hw, hh), (x, y + hh, hw, h - hh), (x + hw, y + hh, w - hw, h - hh)]

class Snapper:
    """Puts each of this PC's game windows in its place on the desktop as it appears (Windows only)."""
    SWP_NOZORDER, SWP_NOACTIVATE, SWP_FRAMECHANGED, SW_RESTORE, SW_MAXIMIZE = 0x0004, 0x0010, 0x0020, 9, 3
    GWL_STYLE = -16
    FRAME = 0x00C00000 | 0x00040000 | 0x00080000 | 0x00020000 | 0x00010000   # caption, sizing border, menu, min, max

    def _borderless(self, h):
        """Takes away the window's title bar and border, so the game fills its whole rectangle."""
        get = getattr(self.u32, "GetWindowLongW")
        st = get(h, self.GWL_STYLE)
        if st & self.FRAME:
            self.u32.SetWindowLongW(h, self.GWL_STYLE, st & ~self.FRAME)

    def __init__(self):
        self.jobs = []                  # dict(pid, k, n, t0, done)
        self.ok = IS_WIN
        if self.ok:
            try:
                self.u32 = ctypes.windll.user32
                try:
                    self.u32.SetProcessDPIAware()           # positions in real screen pixels
                except Exception:
                    pass
            except Exception:
                self.ok = False

    def add(self, pid, k, n):
        if self.ok and pid:
            self.jobs.append(dict(pid=pid, k=k, n=n, t0=now(), done=0))

    def _window_of(self, pid):
        found = []
        u32 = self.u32
        proto = ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_void_p, ctypes.c_void_p)
        def cb(hwnd, _):
            p = ctypes.c_ulong()
            u32.GetWindowThreadProcessId(ctypes.c_void_p(hwnd), ctypes.byref(p))
            if p.value == pid and u32.IsWindowVisible(ctypes.c_void_p(hwnd)) and \
                    not u32.GetWindow(ctypes.c_void_p(hwnd), 4):          # GW_OWNER: a main window
                found.append(hwnd)
                return False
            return True
        u32.EnumWindows(proto(cb), 0)
        return found[0] if found else None

    def poll(self, t):
        if not self.jobs:
            return
        class RECT(ctypes.Structure):
            _fields_ = [("l", ctypes.c_long), ("t", ctypes.c_long), ("r", ctypes.c_long), ("b", ctypes.c_long)]
        wa = RECT()
        self.u32.SystemParametersInfoW(0x30, 0, ctypes.byref(wa), 0)      # SPI_GETWORKAREA: above the taskbar
        for j in list(self.jobs):
            age = t - j["t0"]
            # The game creates its renderer at its own resolution while it starts, after the first placement,
            # so the picture is stretched until it is told the window's size again: placed again a few times,
            # each time with a size message, which makes the game resize its buffers to the window (its
            # WM_SIZE handler reads the client area). Also covers the game sizing its window itself.
            due = (0, 4, 10, 18, 30, 45)
            if age > 75 or j["done"] >= len(due):
                self.jobs.remove(j)
                continue
            if age < due[j["done"]]:
                continue
            hwnd = self._window_of(j["pid"])
            if not hwnd:
                continue
            h = ctypes.c_void_p(hwnd)
            self.u32.ShowWindow(h, self.SW_RESTORE)
            self._borderless(h)                             # no title bars: the screen is split like a console's
            if j["n"] <= 1:
                # one window: the whole screen, over the taskbar too
                x, y, w, hh = 0, 0, self.u32.GetSystemMetrics(0), self.u32.GetSystemMetrics(1)
            else:
                x, y, w, hh = split_rects(j["n"], wa.l, wa.t, wa.r - wa.l, wa.b - wa.t)[min(j["k"], j["n"] - 1)]
            self.u32.SetWindowPos(h, None, x, y, w, hh, self.SWP_NOZORDER | self.SWP_NOACTIVATE | self.SWP_FRAMECHANGED)
            kind = 0                                        # SIZE_RESTORED
            cr = RECT()
            self.u32.GetClientRect(h, ctypes.byref(cr))
            cw, ch = cr.r - cr.l, cr.b - cr.t
            if cw > 0 and ch > 0:
                # WM_SIZE even when the size did not change: the game then matches its picture to the window
                self.u32.PostMessageW(h, 0x0005, kind, (ch & 0xFFFF) << 16 | (cw & 0xFFFF))
            j["done"] += 1

GO_SPACING = 12.0                       # at most this many seconds between a PC's windows started by the room
                                        # host's launch; usually the next starts as soon as the last has read
                                        # init.txt (about 2 s), see Engine._window_read_init

def window_name(base, k):
    """A PC's k-th game window (0 = first) as the room and the game show it: "Name", "Name (1)", "Name (2)" ...
    At most 16 characters (a Halo 2 player name), no quotes or backslashes (it goes into a console line)."""
    base = re.sub(r'["\\\x00-\x1f]', "", str(base)).strip() or "Player"
    if k <= 0:
        return base[:16]
    tail = " (%d)" % k
    return base[:16 - len(tail)].rstrip() + tail

# ---- game files: H2Link's changes to H2EK files, applied to the player's own copies -------------------
# patches/patches.json lists {"file": made or changed (relative to the game folder), "from": the original it is
# made from, "patch": file in patches/}. A file changed in place is backed up first (h2link_backup in the game
# folder) and later patches are made from that backup, so updates and uninstalling always start from the original.
import zlib

H2P_MAGIC = b"H2P1"

def patch_make(src, dst, gap=16):
    recs, i, n = [], 0, min(len(src), len(dst))
    while i < n:
        if src[i] == dst[i]:
            i += 1
            continue
        j = i
        while j < n:                              # extend over short equal runs, so records stay few
            if src[j] != dst[j]:
                j += 1
                continue
            k = j
            while k < n and k - j < gap and src[k] == dst[k]:
                k += 1
            if k < n and k - j < gap:
                j = k
            else:
                break
        recs.append((i, dst[i:j]))
        i = j
    if len(dst) > n:
        recs.append((n, dst[n:]))
    body = b"".join(struct.pack("<II", o, len(b)) + b for o, b in recs)
    head = json.dumps(dict(src_sha256=hashlib.sha256(src).hexdigest(), src_size=len(src),
                           dst_sha256=hashlib.sha256(dst).hexdigest(), dst_size=len(dst))).encode()
    return H2P_MAGIC + struct.pack("<I", len(head)) + head + zlib.compress(body, 9)

def patch_info(patch):
    if patch[:4] != H2P_MAGIC:
        raise ValueError("not an H2Link patch")
    hl = struct.unpack_from("<I", patch, 4)[0]
    return json.loads(patch[8:8 + hl].decode())

def patch_apply(patch, src):
    h = patch_info(patch)
    if hashlib.sha256(src).hexdigest() != h["src_sha256"]:
        raise ValueError("the file is not the expected original")
    hl = struct.unpack_from("<I", patch, 4)[0]
    body = zlib.decompress(patch[8 + hl:])
    out = bytearray(src[:h["dst_size"]].ljust(h["dst_size"], b"\0"))
    p = 0
    while p < len(body):
        o, ln = struct.unpack_from("<II", body, p); p += 8
        out[o:o + ln] = body[p:p + ln]; p += ln
    out = bytes(out)
    if hashlib.sha256(out).hexdigest() != h["dst_sha256"]:
        raise ValueError("the patched file did not come out as expected")
    return out

# ---- the retail loading screen: Project Cartographer's loading.bin -> loading_dx11.bin ---------------------
# loading.bin holds 12 BMPs (Halo 2 PC's loading screen). The game's own (MCC) loading screen reads 6 images from
# loading_dx11.bin as uncompressed A8R8G8B8 DDS, at the offsets its table expects (exe v65+): background
# 1280x1024, HALO 2 logo 1024x128, two rings 512x512, progress strip 2048x4, logo glow 512x512. The 32-bit
# images keep their alpha; the 24-bit rings and glow take alpha = max(R, G, B), the background is opaque.
LOADING_SLOTS = ((0, "opaque"), (1, "keep"), (3, "max"), (4, "max"), (5, "keep"), (11, "max"))
LOADING_SHA256 = "ad95abeb2ac043f48ec7"        # start of the known-good result's SHA-256 (made from PC's loading.bin)

def loading_dx11(src):
    """loading_dx11.bin made from loading.bin's bytes."""
    bmps, p = [], 0
    while p + 54 <= len(src) and src[p:p + 2] == b"BM":
        size, off = struct.unpack_from("<I", src, p + 2)[0], struct.unpack_from("<I", src, p + 10)[0]
        w, h = struct.unpack_from("<ii", src, p + 18)
        bmps.append((w, h, struct.unpack_from("<H", src, p + 28)[0], src[p + off:p + size]))
        p += size
    if len(bmps) < 12:
        raise ValueError("loading.bin should hold 12 pictures, it has %d" % len(bmps))
    out = bytearray()
    for i, alpha in LOADING_SLOTS:
        w, h, bpp, px = bmps[i]
        hd = bytearray(128)
        hd[0:4] = b"DDS "
        struct.pack_into("<7I", hd, 4, 124, 0x100F, h, w, w * 4, 0, 1)
        struct.pack_into("<8I", hd, 76, 32, 0x41, 0, 32, 0xFF0000, 0xFF00, 0xFF, 0xFF000000)
        struct.pack_into("<I", hd, 108, 0x1000)
        stride, row_bytes = ((w * bpp // 8) + 3) & ~3, w * bpp // 8
        img = bytearray(w * h * 4)
        for y in range(h):                                  # BMP rows run bottom-up, DDS rows top-down
            row = px[(h - 1 - y) * stride:(h - 1 - y) * stride + row_bytes]
            o = y * w * 4
            if bpp == 32:
                img[o:o + w * 4] = row
            else:
                q = img[o:o + w * 4]
                q[0::4], q[1::4], q[2::4] = row[0::3], row[1::3], row[2::3]
                q[3::4] = bytes([255]) * w if alpha == "opaque" else bytes(map(max, row[0::3], row[1::3], row[2::3]))
                img[o:o + w * 4] = q
        out += hd + img
    return bytes(out)

def saved_profiles():
    """The Halo 2 profiles saved on this PC, as lower-case names: the game keeps each as <name>.Halo2 in
    Saved Games\\MCCH2. None if that folder is not there (then H2Link cannot tell, and passes the name on)."""
    roots = []
    if IS_WIN:
        try:                                            # the Saved Games folder, wherever it was moved to
            class GUID(ctypes.Structure):
                _fields_ = [("a", ctypes.c_ulong), ("b", ctypes.c_ushort), ("c", ctypes.c_ushort), ("d", ctypes.c_ubyte * 8)]
            g = GUID(0x4C5C32FF, 0xBB9D, 0x43B0, (ctypes.c_ubyte * 8)(0xB5, 0xB4, 0x2D, 0x72, 0xE5, 0x4E, 0xAA, 0xA4))
            p = ctypes.c_wchar_p()
            if ctypes.windll.shell32.SHGetKnownFolderPath(ctypes.byref(g), 0, None, ctypes.byref(p)) == 0:
                roots.append(p.value)
                ctypes.windll.ole32.CoTaskMemFree(p)
        except Exception:
            pass
    roots.append(os.path.join(os.path.expanduser("~"), "Saved Games"))
    for r in roots:
        for d in (os.path.join(r, "MCCH2"), os.path.join(r, "Microsoft", "MCCH2", "Saved Games")):
            if os.path.isdir(d):
                return {f[:-6].lower() for f in os.listdir(d) if f.lower().endswith(".halo2")}
    return None

def patches_dir():
    base = getattr(sys, "_MEIPASS", None) or os.path.dirname(os.path.abspath(sys.argv[0]))
    return os.path.join(base, "patches")

def _sha_file(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()

def _game_plan(game_dir, say):
    """For each game file: what install_game would do. Returns (items, problems): every item gets "state"
    ("up to date" or "make", with "orig" and "patch" for the latter); problems lists the files that cannot
    be made because the H2EK original is not there (not in place and not in h2link_backup)."""
    pdir = patches_dir()
    with open(os.path.join(pdir, "patches.json")) as f:
        items = json.load(f)
    bdir = os.path.join(game_dir, "h2link_backup")
    problems = []
    for it in items:
        dst = os.path.join(game_dir, it["file"])
        with open(os.path.join(pdir, it["patch"]), "rb") as f:
            it["patch_data"] = f.read()
        h = patch_info(it["patch_data"])
        if os.path.isfile(dst) and _sha_file(dst) == h["dst_sha256"]:
            it["state"] = "up to date"
            continue
        for cand in (os.path.join(bdir, it["from"]), os.path.join(game_dir, it["from"])):
            if os.path.isfile(cand) and _sha_file(cand) == h["src_sha256"]:
                it["state"], it["orig"] = "make", cand
                break
        else:
            it["state"] = "missing"
            src = os.path.join(game_dir, it["from"])
            problems.append("%s - %s" % (os.path.normpath(src),
                            "not found" if not os.path.isfile(src) else
                            "%d bytes, SHA-256 %s... (the original is %d bytes, %s...)" % (
                                os.path.getsize(src), _sha_file(src)[:12], h["src_size"], h["src_sha256"][:12])))
    return items, problems

def install_game(game_dir, say=print, check_only=False):
    """Makes or updates H2Link's game files in game_dir: all of them, or - when an H2EK original is missing -
    none at all. Returns 0 when everything is (or, with check_only, can be) in place."""
    try:
        items, problems = _game_plan(game_dir, say)
    except (OSError, ValueError, KeyError) as e:
        say("Cannot read H2Link's game-file patches (%s)" % e)
        return 1
    if problems:
        for f in problems:
            say("  NOT THE ORIGINAL  %s" % f)
        say("Nothing was changed. Let Steam put the H2EK's original files back: Library > H2EK > Properties > "
            "Installed Files > Verify integrity of tool files. Then install H2Link again.")
        return 1
    if check_only:
        say("All H2EK files H2Link needs are in place.")
        return 0
    bdir = os.path.join(game_dir, "h2link_backup")
    bad = 0
    for it in items:
        if it["state"] == "up to date":
            say("  up to date      %s" % it["file"])
            continue
        dst = os.path.join(game_dir, it["file"])
        try:
            with open(it["orig"], "rb") as f:
                orig = f.read()
            out = patch_apply(it["patch_data"], orig)
            bak = os.path.join(bdir, it["from"])
            if it["file"] == it["from"] and not os.path.isfile(bak):
                os.makedirs(os.path.dirname(bak), exist_ok=True)
                with open(bak, "wb") as f:
                    f.write(orig)
            os.makedirs(os.path.dirname(dst) or ".", exist_ok=True)
            with open(dst + ".h2link_new", "wb") as f:
                f.write(out)
            os.replace(dst + ".h2link_new", dst)
            say("  installed       %s" % it["file"])
        except (OSError, ValueError) as e:
            say("  NOT CHANGED     %s: %s" % (it["file"], e))
            bad += 1
    return 1 if bad else 0

def restore_game(game_dir, say=print):
    """Puts the H2EK originals back and removes the files H2Link made."""
    bdir = os.path.join(game_dir, "h2link_backup")
    try:
        with open(os.path.join(patches_dir(), "patches.json")) as f:
            items = json.load(f)
    except (OSError, ValueError):
        items = []
    for it in items:
        if it["file"] != it["from"]:
            try:
                os.remove(os.path.join(game_dir, it["file"]))
                say("  removed         %s" % it["file"])
            except OSError:
                pass
    for d, _, files in os.walk(bdir):
        for fn in files:
            b = os.path.join(d, fn)
            rel = os.path.relpath(b, bdir)
            try:
                os.makedirs(os.path.dirname(os.path.join(game_dir, rel)) or ".", exist_ok=True)
                shutil.copyfile(b, os.path.join(game_dir, rel))
                say("  restored        %s" % rel)
            except OSError as e:
                say("  NOT RESTORED    %s: %s" % (rel, e))
    shutil.rmtree(bdir, ignore_errors=True)
    return 0

# ---- its own window ------------------------------------------------------------------------------------
# The control page opens as an app window of Microsoft Edge (on every Windows PC) or Chrome: no tabs, no
# address bar, its own taskbar entry and icon. Elsewhere, or if neither is found, the default browser.
ICON_ICO = base64.b64decode("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")

def app_browser():
    if not IS_WIN:
        return None
    roots = [os.environ.get(k, "") for k in ("ProgramFiles(x86)", "ProgramFiles", "LOCALAPPDATA")]
    for rel in (r"Microsoft\Edge\Application\msedge.exe", r"Google\Chrome\Application\chrome.exe"):
        for r in roots:
            p = os.path.join(r, rel) if r else ""
            if p and os.path.isfile(p):
                return p
    return None

PAGE_WINDOW = [None]                    # the Edge/Chrome app window H2Link opened, to close it with H2Link

def open_page(url):
    """The control page in its own app window, else in the default browser. The app window gets a browser
    profile of its own (in H2Link's folder), so it is a separate browser process that H2Link can close when
    it closes - Close H2Link then closes the window too."""
    exe = app_browser()
    if exe:
        try:
            prof = os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), "page_window")
            if PAGE_WINDOW[0] and PAGE_WINDOW[0].poll() is None:
                close_page_window()
            PAGE_WINDOW[0] = subprocess.Popen([exe, "--app=" + url, "--window-size=1280,1000", "--no-first-run",
                                               "--no-default-browser-check", "--user-data-dir=" + prof],
                                              env=clean_env())
            return
        except OSError:
            pass
    webbrowser.open(url)

def close_page_window():
    """Closes the app window open_page opened (nothing to do for a plain browser tab)."""
    p, PAGE_WINDOW[0] = PAGE_WINDOW[0], None
    if not p or p.poll() is not None:
        return
    try:
        if IS_WIN:                               # the window's whole browser process tree
            subprocess.run(["taskkill", "/PID", str(p.pid), "/T", "/F"], env=clean_env(),
                           capture_output=True, timeout=5, creationflags=0x08000000)
        else:
            p.terminate()
    except Exception:
        pass

SHOW_WINDOW = [None]                    # set while H2Link.exe shows its own window: brings it to the front

def show_running(url):
    """Asks an H2Link already running on this PC to bring its own window up. True if it did."""
    try:
        html = urllib.request.urlopen(url, timeout=1).read().decode("utf-8", "replace")
        tok = re.search(r'TOKEN="([0-9a-f]+)"', html).group(1)
        req = urllib.request.Request(url + "api/show", data=b"{}", method="POST",
                                     headers={"X-H2Link": tok, "Content-Type": "application/json"})
        return bool(json.load(urllib.request.urlopen(req, timeout=2)).get("shown"))
    except Exception:
        return False

def clean_env():
    """This process's environment without PyInstaller's own variables, for starting other programs - above
    all another H2Link.exe, which would otherwise try to use this one's temporary folder."""
    env = {k: v for k, v in os.environ.items()
           if not (k.startswith("_PYI") or k.startswith("_MEI") or k == "_MEIPASS2")}
    env["PYINSTALLER_RESET_ENVIRONMENT"] = "1"
    return env

def hide_console():
    """H2Link.exe as an app: its console window out of sight (the page has the activity list)."""
    if IS_WIN and getattr(sys, "frozen", False):
        try:
            h = ctypes.windll.kernel32.GetConsoleWindow()
            if h:
                ctypes.windll.user32.ShowWindow(h, 0)
        except Exception:
            pass

def listed_tags(data):
    """How many spawned tags an exe v38+ host listed at the end of its join save; None if it has no list."""
    if len(data) >= 12 and data[-8:-4] in (b"H2TG", b"H2T3", b"H2T4"):
        return struct.unpack_from("<I", data, len(data) - 12)[0]
    return None


def list_text(n):
    return "no tag list (host exe older than v38)" if n is None else "lists %d spawned tag%s" % (n, "" if n == 1 else "s")


SAVE_NAME_RE = re.compile(r"^[A-Za-z0-9_\-]{1,48}$")
MAX_SAVE = 32 << 20

# ---- starting the level from the page (needs exe v36 or newer) -------------
# The exe reads init.txt at launch. Its built-in automation then opens or finds the system link
# session by name; v36 taught it campaign: variant type 11-14 = easy..legendary, map = number below.
LEVELS_ALL = ((1, "The Heretic"), (101, "The Armory"), (105, "Cairo Station"), (301, "Outskirts"), (305, "Metropolis"),
          (401, "The Arbiter"), (405, "The Oracle"), (501, "Delta Halo"), (505, "Regret"), (601, "Sacred Icon"),
          (605, "Quarantine Zone"), (701, "Gravemind"), (705, "Uprising"), (801, "High Charity"),
          (805, "The Great Journey"))
LEVEL_NAME = dict(LEVELS_ALL)
# The two training levels are not built for co-op, so the page does not offer them. They still count as
# valid in a plan, so a room host on an older H2Link that picked one does not leave this one waiting.
LEVELS = tuple(l for l in LEVELS_ALL if l[0] not in (1, 101))
DIFFICULTIES = ("Easy", "Normal", "Heroic", "Legendary")
TICKS = ((30, "Classic/30"), (60, "MCC/60"))
TICK_NAME = dict(TICKS)
AUTO_EXE = 36
TICK_BYTE = 0x4CF6F3 - 0x401000 + 0x400     # the exe sets its tick rate with "push N" here: 30 or 60
# Skulls as grouped in the debug menu; each is the game's own on/off global debug_ice_cream_flavor_status_<key>.
SKULLS = (
    ("Classic", (("thats_just_wrong", "That's just...wrong"), ("thunderstorm", "Thunderstorm"), ("blind", "Blind"),
                 ("i_would_have_been_your_daddy", "I would have been your daddy"), ("catch", "Catch"),
                 ("grunt_birthday_party", "Grunt Birthday Party"), ("famine", "Famine"), ("arbiter_envy", "Envy"),
                 ("assassins", "Assassins"), ("mythic", "Mythic"), ("sputnik", "Sputnik"), ("anger", "Anger"),
                 ("ghost", "Ghost"), ("iron", "Iron"), ("black_eye", "Black Eye"))),
    ("HCEA", (("bandanna", "Bandana"), ("boom", "Boom"), ("eye_patch", "Eye Patch"), ("fog", "Fog"),
              ("foreign", "Foreign"), ("grunt_funeral", "Grunt Funeral"), ("malfunction", "Malfunction"),
              ("pinata", "Pinata"), ("recession", "Recession"))),
    ("H2A", (("feather", "Feather"), ("jacked", "Jacked"), ("prophet_birthday_party", "Prophet Birthday Party"),
             ("scarab", "Scarab"), ("so_angry", "SO...ANGRY..."), ("streaking", "Streaking"), ("styx", "Styx"),
             ("they_come_back", "They Come Back"), ("bonded_pair", "Bonded Pair (coop)"),
             ("masterblaster", "Masterblaster (coop)"))),
)
SKULL_NAME = {k: n for _, items in SKULLS for k, n in items}
INIT_ALWAYS = ("error_geometry_hide_all", "console_status_string_render off", "terminal_render off")
INIT_CHEATS_ON = ("cheat_controller on",)
INIT_CHEATS_OFF = ("cheat_controller off", "debug_menu_enabled off")
# lines H2Link writes itself; dropped from the player's own lines so they cannot contradict the room's
INIT_OURS = ("ui_set_automation_", "net_test_", "cheat_controller", "debug_menu_enabled", "debug_ice_cream_flavor_",
             "error_geometry_hide_all", "console_status_string_render", "terminal_render")


def slot_text(slots):
    """Slots as players see them: 01-16. The game's log files keep its own 00-15 (s00...s15)."""
    return ", ".join("%02d" % (x + 1) for x in slots)


def clean_plan(d, base=None):
    """A valid room plan from untrusted input, or None."""
    try:
        plan = dict(base or dict(level=105, diff=1, tick=30, cheats=True, skulls=[]))
        if "level" in d:
            plan["level"] = int(d["level"])
        if "diff" in d or "difficulty" in d:
            plan["diff"] = int(d.get("diff", d.get("difficulty")))
        if "tick" in d:
            plan["tick"] = int(d["tick"])
        if "cheats" in d:
            plan["cheats"] = bool(d["cheats"])
        if "skulls" in d:
            plan["skulls"] = [k for k in SKULL_NAME if k in set(map(str, d["skulls"]))]
    except (TypeError, ValueError):
        return None
    if plan["level"] not in LEVEL_NAME or not 0 <= plan["diff"] < len(DIFFICULTIES) or plan["tick"] not in TICK_NAME:
        return None
    return plan


def plan_text(plan):
    return "%s on %s, %s, debug menu and cheats %s, %s" % (
        LEVEL_NAME[plan["level"]], DIFFICULTIES[plan["diff"]], TICK_NAME[plan["tick"]],
        "on" if plan["cheats"] else "off",
        "skulls: " + ", ".join(SKULL_NAME[k] for k in plan["skulls"]) if plan["skulls"] else "no skulls")


# ---- tunnel protocol -------------------------------------------------------
DEFAULT_PORT = 31100
UI_PORT = 31180
MAGIC = b"H2LK"
T_HELLO, T_CHALLENGE, T_AUTH, T_WELCOME, T_REJECT, T_LIST, T_ROOMS = 1, 2, 3, 4, 5, 6, 7
T_PING, T_PONG, T_BYE, T_DATA, T_REL, T_RACK = 0x10, 0x11, 0x12, 0x20, 0x30, 0x31
M_ROSTER, M_PAGE_G, M_PAGE_P, M_EVENT, M_JSYNC, M_JSYNC_PUB, M_JSYNC_LOADED, M_ROOM, M_LANE, M_LIVE, M_ROLE, M_CHAT, M_GO = 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13
M_AUTO = 14
M_CHATLOG = 15                          # the room's chat so far, from the room host to a PC that joins (1.0.14+)                             # "my game starts when the room host launches": 1 or 0 (1.0.8+)
HDR = struct.Struct("<BBB4s")
REL_HDR = struct.Struct("<BBB4sIIIB")
RACK_HDR = struct.Struct("<BBB4sIIIQ")
PING_HDR = struct.Struct("<BBB4sIH")
JS_HDR = struct.Struct("<IIIII64s")     # sync seq, sender, next update, raw len, crc, name
FRAG = 1100
DIRECT_TIMEOUT = 5.0
HOST_SILENT = 10.0
NODE_SILENT = 15.0


def now():
    return time.monotonic()


DUPLICATE = ("Another PC in this room is using the same H2Link identity, which happens when the H2Link folder "
             "is copied together with its h2link.json. Close H2Link on this PC, delete h2link.json in its folder "
             "and start it again. To run two copies on one PC, give the second its own file with --config.")


def machine_mark():
    """A short mark for this PC, so a settings file copied to another PC is noticed."""
    try:
        node = uuid_mod.getnode()
        if (node >> 40) & 1:            # no real network card found: Python made a random number, useless here
            node = 0
    except Exception:
        node = 0
    return hashlib.sha256(("%s|%x" % (platform.node(), node)).encode()).hexdigest()[:16]


IDLE_EXIT = 180.0           # no page open and nothing depending on H2Link for this long: it closes


def running_instance(port):
    """The page address of an H2Link that is already running on this PC, or None."""
    for p in (port, port + 1):
        try:
            with urllib.request.urlopen("http://127.0.0.1:%d/api/state" % p, timeout=0.4) as r:
                if json.load(r).get("app") == APP:
                    return "http://127.0.0.1:%d/" % p
        except Exception:
            continue
    return None


def console_title(text):
    if IS_WIN:
        try:
            ctypes.WinDLL("kernel32").SetConsoleTitleW(text)
        except Exception:
            pass


def quiet_console():
    """Windows: switch off QuickEdit, where a click in the console window freezes the program."""
    if not IS_WIN:
        return
    try:
        k32 = ctypes.WinDLL("kernel32")
        k32.GetStdHandle.restype = ctypes.c_void_p
        k32.GetStdHandle.argtypes = [ctypes.c_uint32]
        k32.GetConsoleMode.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint32)]
        k32.SetConsoleMode.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
        h = k32.GetStdHandle(0xFFFFFFF6)             # STD_INPUT_HANDLE
        mode = ctypes.c_uint32()
        if h and k32.GetConsoleMode(h, ctypes.byref(mode)):
            k32.SetConsoleMode(h, (mode.value & ~0x0040) | 0x0080)
    except Exception:
        pass


def split_addr(text, default_port=DEFAULT_PORT):
    """'host' or 'host:port' -> (host, port)."""
    text = text.strip()
    host, _, port = text.rpartition(":") if ":" in text else (text, "", "")
    return host, int(port) if port else default_port


KEY_PREFIX = "H2L1-"
KEY_DAMAGED = ("The server key is not complete or was mistyped. Copy the whole line that --make-key printed; "
               "after H2L1- it holds only the letters A-Z and the digits 2-7.")
KEY_NO_NAME = ("The server key is intact, but the server name inside it cannot be looked up from this PC. "
               "The key was probably made from a name that does not exist; make a new one from the server's real address.")
IP_RE = re.compile(r"\b\d{1,3}(?:\.\d{1,3}){3}\b")


def _key_stream(nonce, n):
    out, i = b"", 0
    while len(out) < n:
        out += hashlib.sha256(b"h2link-server-key|" + nonce + bytes([i])).digest()
        i += 1
    return out[:n]


def make_server_key(address):
    """Scramble a server address into a key for server.key. This keeps the address out of
    sight in files and on the page; it is not secrecy, since a PC's connections can be watched."""
    host, port = split_addr(address)
    raw = ("%s:%d" % (host, port)).encode()
    nonce = os.urandom(4)
    body = hashlib.sha256(raw).digest()[:2] + raw
    mixed = bytes(a ^ b for a, b in zip(body, _key_stream(nonce, len(body))))
    return KEY_PREFIX + base64.b32encode(nonce + mixed).decode().rstrip("=")


def read_server_key(text):
    """The address inside a server key, or None if `text` is not a valid key."""
    text = text.strip()
    if not text.upper().startswith(KEY_PREFIX):
        return None
    try:
        b32 = text[len(KEY_PREFIX):].upper()
        blob = base64.b32decode(b32 + "=" * (-len(b32) % 8))
        nonce, mixed = blob[:4], blob[4:]
        body = bytes(a ^ b for a, b in zip(mixed, _key_stream(nonce, len(mixed))))
        if len(body) < 4 or hashlib.sha256(body[2:]).digest()[:2] != body[:2]:
            return None
        return body[2:].decode()
    except (ValueError, UnicodeDecodeError):
        return None


def server_target(text):
    """(host, port, hidden) for what is in the Server setting: a key or a plain address."""
    inner = read_server_key(text)
    if inner is None and text.strip().upper().startswith(KEY_PREFIX):
        raise ValueError("damaged server key")
    host, port = split_addr(inner if inner is not None else text)
    return host, port, inner is not None


def room_key_of(password):
    return hashlib.sha256(b"h2link-room|" + (password or "").encode()).digest()


def clean_room(name):
    return " ".join(str(name).split())[:32]


def alloc_slots(used, reserved, want, pref, uuid):
    """Pick `want` free slots for one PC: the ones it asks for or held before, then the lowest free.
    Slots held back for PCs that left are only taken when nothing else is free."""
    resv = set()
    for u, sl in reserved.items():
        if u != uuid:
            resv |= set(sl)
    out = []
    for s in list(pref) + list(reserved.get(uuid, [])):
        if isinstance(s, int) and 0 <= s < NSLOTS and s not in used and s not in resv and s not in out and len(out) < want:
            out.append(s)
    for avoid in (resv, ()):
        for s in range(NSLOTS):
            if len(out) < want and s not in used and s not in avoid and s not in out:
                out.append(s)
    if len(out) < want:
        return None
    for u in list(reserved):
        if u != uuid and set(reserved[u]) & set(out):
            del reserved[u]
    reserved[uuid] = sorted(out)
    return sorted(out)


class Log:
    """Keeps the session's lines and prints them from its own thread. A console window that is
    paused (text selected in it, or a slow terminal) must never stall the tunnel or the server."""

    def __init__(self, echo=True):
        self.items = collections.deque(maxlen=6000)
        self.lock = threading.Lock()
        self.echo = echo
        self.seq = 0
        self.out = queue.SimpleQueue()
        if echo:
            quiet_console()
            threading.Thread(target=self._printer, daemon=True).start()

    def _printer(self):
        while True:
            line = self.out.get()
            try:
                print(line, flush=True)
            except Exception:
                pass

    def add(self, level, text):
        with self.lock:
            self.seq += 1
            self.items.append((self.seq, time.time(), level, text))
        if self.echo:
            self.out.put("%s %-5s %s" % (time.strftime("%H:%M:%S"), level, text))

    def flush(self, wait=1.0):
        end = time.time() + wait
        while not self.out.empty() and time.time() < end:
            time.sleep(0.02)

    def info(self, t): self.add("info", t)
    def warn(self, t): self.add("warn", t)
    def error(self, t): self.add("error", t)

    def tail(self, n=120):
        with self.lock:
            return [list(x) for x in list(self.items)[-n:]]

    def text(self):
        with self.lock:
            return "\r\n".join("%s %-5s %s" % (time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(i[1])), i[2], i[3])
                               for i in self.items)


# ===========================================================================
# OS glue: slot mutexes, the shared page, atomic writes into it
# ===========================================================================
class AtomicOps:
    """lock add / lock or / lock and on the page. The game changes the same
    bytes with locked instructions, so plain read-modify-write could lose one."""

    def __init__(self):
        self.ok = False
        if os.environ.get("H2LINK_NO_ATOMIC"):
            return
        mach = platform.machine().lower()
        bits = struct.calcsize("P") * 8
        x86 = mach in ("amd64", "x86_64", "x86", "i386", "i686")
        if not x86:
            return
        if IS_WIN and bits == 64:        # rcx = address, edx = operand
            add, or8, and8 = b"\xf0\x01\x11\xc3", b"\xf0\x08\x11\xc3", b"\xf0\x20\x11\xc3"
        elif IS_WIN and bits == 32:      # cdecl: [esp+4] = address, [esp+8] = operand
            pre = b"\x8b\x44\x24\x04\x8b\x54\x24\x08"
            add, or8, and8 = pre + b"\xf0\x01\x10\xc3", pre + b"\xf0\x08\x10\xc3", pre + b"\xf0\x20\x10\xc3"
        elif not IS_WIN and bits == 64:  # rdi = address, esi = operand
            add, or8, and8 = b"\xf0\x01\x37\xc3", b"\xf0\x40\x08\x37\xc3", b"\xf0\x40\x20\x37\xc3"
        else:
            return
        try:
            code = add.ljust(16, b"\xcc") + or8.ljust(16, b"\xcc") + and8.ljust(16, b"\xcc")
            if IS_WIN:
                k32 = ctypes.WinDLL("kernel32")
                k32.VirtualAlloc.restype = ctypes.c_void_p
                k32.VirtualAlloc.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_uint32, ctypes.c_uint32]
                base = k32.VirtualAlloc(None, 4096, 0x3000, 0x40)
                if not base:
                    return
                ctypes.memmove(base, code, len(code))
            else:
                self._mem = mmap.mmap(-1, 4096, prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC)
                self._mem[:len(code)] = code
                self._ref = (ctypes.c_ubyte * 4096).from_buffer(self._mem)
                base = ctypes.addressof(self._ref)
            proto = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.c_uint32)
            self.add = proto(base)
            self.or8 = proto(base + 16)
            self.and8 = proto(base + 32)
            probe = (ctypes.c_uint32 * 2)(0x00F0, 0)
            a = ctypes.addressof(probe)
            self.add(a, 5)
            self.or8(a, 0x0A)
            self.and8(a, 0xFE)
            self.ok = probe[0] == 0x00FE and probe[1] == 0
        except Exception:
            self.ok = False


class Platform:
    def __init__(self, page_file=None):
        self.page_file = page_file          # test mode: a file stands in for the named page
        self.win = IS_WIN and not page_file
        self.atomic = AtomicOps()
        if self.win:
            k = self.k32 = ctypes.WinDLL("kernel32", use_last_error=True)
            k.CreateMutexW.restype = ctypes.c_void_p
            k.CreateMutexW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_wchar_p]
            k.OpenMutexW.restype = ctypes.c_void_p
            k.OpenMutexW.argtypes = [ctypes.c_uint32, ctypes.c_int, ctypes.c_wchar_p]
            k.CloseHandle.argtypes = [ctypes.c_void_p]
            try:
                ctypes.WinDLL("winmm").timeBeginPeriod(1)   # 1 ms timer so short waits are short
            except Exception:
                pass
        elif page_file:
            os.makedirs(page_file + ".slots", exist_ok=True)

    def _slot_file(self, slot):
        return os.path.join(self.page_file + ".slots", "slot%02d" % slot)

    def claim_mutex(self, slot):
        if self.win:
            return self.k32.CreateMutexW(None, 0, MUTEX_FMT % slot)
        if self.page_file:
            open(self._slot_file(slot), "a").close()
            return slot + 1
        return None

    def release_mutex(self, slot, handle):
        if self.win and handle:
            self.k32.CloseHandle(handle)
        elif self.page_file:
            try:
                os.remove(self._slot_file(slot))
            except OSError:
                pass

    def mutex_exists(self, slot):
        if self.win:
            h = self.k32.OpenMutexW(0x00100000, 0, MUTEX_FMT % slot)
            if h:
                self.k32.CloseHandle(h)
                return True
            return False
        if self.page_file:
            return os.path.exists(self._slot_file(slot))
        return False

    @staticmethod
    def no_connreset(_self, sock):
        """Windows reports an ICMP port-unreachable as an error on the next
        recvfrom of a UDP socket; switch that off (it is also caught)."""
        if not IS_WIN:
            return
        try:
            ws2 = ctypes.WinDLL("ws2_32")
            ws2.WSAIoctl.argtypes = [ctypes.c_size_t, ctypes.c_uint32, ctypes.c_void_p, ctypes.c_uint32,
                                     ctypes.c_void_p, ctypes.c_uint32, ctypes.POINTER(ctypes.c_uint32),
                                     ctypes.c_void_p, ctypes.c_void_p]
            flag, ret = ctypes.c_uint32(0), ctypes.c_uint32(0)
            ws2.WSAIoctl(sock.fileno(), 0x9800000C, ctypes.byref(flag), 4, None, 0, ctypes.byref(ret), None, None)
        except Exception:
            pass


class Page:
    """The 4 KB page every game instance on this PC polls once per frame."""

    def __init__(self, plat):
        if plat.win:
            self.mm = mmap.mmap(-1, PAGE_SIZE, tagname=PAGE_NAME)
        elif plat.page_file:
            if not os.path.exists(plat.page_file) or os.path.getsize(plat.page_file) != PAGE_SIZE:
                with open(plat.page_file, "wb") as f:
                    f.write(b"\0" * PAGE_SIZE)
            self._f = open(plat.page_file, "r+b")
            self.mm = mmap.mmap(self._f.fileno(), PAGE_SIZE)
        else:
            self.mm = mmap.mmap(-1, PAGE_SIZE)
        self.ops = plat.atomic if plat.atomic.ok else None
        self._arr = (ctypes.c_ubyte * PAGE_SIZE).from_buffer(self.mm)
        self.base = ctypes.addressof(self._arr)

    def close(self):
        try:
            self._arr = None
            self.mm.close()
        except Exception:
            pass

    def u32(self, off):
        return struct.unpack_from("<I", self.mm, off)[0]

    def set_u32(self, off, v):
        struct.pack_into("<I", self.mm, off, v & 0xFFFFFFFF)

    def read(self, off, n):
        return self.mm[off:off + n]

    def write(self, off, data):
        self.mm[off:off + len(data)] = data

    def add_u32(self, off, d):
        if self.ops:
            self.ops.add(self.base + off, d & 0xFFFFFFFF)
        else:
            self.set_u32(off, self.u32(off) + d)

    def or8(self, off, m):
        if self.ops:
            self.ops.or8(self.base + off, m & 0xFF)
        else:
            self.mm[off] = self.mm[off] | (m & 0xFF)

    def and8(self, off, m):
        if self.ops:
            self.ops.and8(self.base + off, m & 0xFF)
        else:
            self.mm[off] = self.mm[off] & (m & 0xFF)


# ===========================================================================
# Reliable, ordered messages over UDP (roster, page mirroring, save transfer)
# ===========================================================================
class RelTx:
    MAXWIN = 512

    def __init__(self):
        self.reset()

    def reset(self):
        self.seq = 0
        self.queue = collections.deque()
        self.inflight = collections.OrderedDict()   # seq -> [packet, last sent, resend count]
        self.cwnd = 32.0
        self.ssthresh = 128.0
        self.srtt = None
        self.rttvar = 0.0
        self.rto = 0.3
        self.loss_until = 0.0

    def idle(self):
        return not self.queue and not self.inflight

    def enqueue(self, msg):
        n, i = len(msg), 0
        while i < n:
            j = min(i + FRAG, n)
            self.queue.append(((1 if i == 0 else 0) | (2 if j == n else 0), msg[i:j]))
            i = j

    def pump(self, t, mk, send):
        win = min(self.cwnd, self.MAXWIN)
        while self.queue and len(self.inflight) < win:
            flags, chunk = self.queue.popleft()
            pkt = mk(self.seq, flags, chunk)
            self.inflight[self.seq] = [pkt, t, 0]
            self.seq += 1
            if not send(pkt):
                break
            if flags == 3:               # a short message has no later packet to expose its loss
                send(pkt)

    def _sample(self, r):
        if self.srtt is None:
            self.srtt, self.rttvar = r, r / 2
        else:
            self.rttvar = 0.75 * self.rttvar + 0.25 * abs(self.srtt - r)
            self.srtt = 0.875 * self.srtt + 0.125 * r
        self.rto = min(2.0, max(0.1, self.srtt + 4 * self.rttvar))

    def _loss(self, t):
        if t >= self.loss_until:
            # Losses on these short bursts are mostly random, so back off gently and keep a floor.
            self.ssthresh = max(self.cwnd * 0.7, 24.0)
            self.cwnd = self.ssthresh
            self.loss_until = t + (self.srtt or 0.2)

    def on_ack(self, t, cum, bitmap, send):
        infl = self.inflight
        acked, sample, hi = 0, None, -1
        while infl:
            s = next(iter(infl))
            if s >= cum:
                break
            ent = infl.pop(s)
            acked += 1
            if ent[2] == 0:
                sample = t - ent[1]
        i = 0
        while bitmap:
            if bitmap & 1:
                s = cum + 1 + i
                hi = s
                ent = infl.pop(s, None)
                if ent is not None:
                    acked += 1
                    if ent[2] == 0:
                        sample = t - ent[1]
            bitmap >>= 1
            i += 1
        if sample is not None:
            self._sample(sample)
        if acked:
            if self.cwnd < self.ssthresh:
                self.cwnd += acked
            else:
                self.cwnd += acked / self.cwnd
        if hi >= 0:                      # holes well below the highest received packet
            n, wait = 0, max(self.srtt or 0.1, 0.03)
            for s, ent in infl.items():
                if s >= hi - 2:
                    break
                if t - ent[1] > wait:
                    send(ent[0])
                    ent[1] = t
                    ent[2] += 1
                    n += 1
                    if n >= 32:
                        break
            if n:
                self._loss(t)

    def tick(self, t, send):
        k = n = 0
        rto = self.rto
        for s, ent in self.inflight.items():
            if t - ent[1] >= rto * (1.5 ** min(ent[2], 4)):
                send(ent[0])
                ent[1] = t
                ent[2] += 1
                n += 1
                if n >= 16:
                    break
            k += 1
            if k >= 64:
                break
        if n:
            self._loss(t)


class RelRx:
    def __init__(self):
        self.reset()

    def reset(self):
        self.expected = 0
        self.buf = {}
        self.parts = []
        self.size = 0
        self.ack_due = False

    def on_pkt(self, seq, flags, payload):
        self.ack_due = True
        if seq < self.expected or seq - self.expected > 8192 or seq in self.buf:
            return ()
        self.buf[seq] = (flags, payload)
        out = []
        while self.expected in self.buf:
            f, p = self.buf.pop(self.expected)
            self.expected += 1
            if f & 1:
                self.parts, self.size = [], 0
            self.parts.append(p)
            self.size += len(p)
            if self.size > MAX_SAVE + (1 << 20):
                self.parts, self.size = [], 0
            elif f & 2:
                out.append(b"".join(self.parts))
                self.parts, self.size = [], 0
        return out

    def ack(self):
        self.ack_due = False
        bm, e, buf = 0, self.expected, self.buf
        if buf:
            for i in range(64):
                if e + 1 + i in buf:
                    bm |= 1 << i
        return e, bm


class Peer:
    def __init__(self, nid):
        self.id = nid
        self.name = "?"
        self.hosting = False            # its game was started as the room's host and is still running
        self.epoch = 0
        self.slots = []
        self.cands = []
        self.addr = None                # confirmed direct address
        self.last_rx = 0.0              # last packet that arrived straight from addr
        self.rtt = None
        self.rtt_relay = None
        self.games = 0                  # bitmap of that PC's slots with a game running
        self.tokens = collections.OrderedDict()
        self.next_ping = 0.0
        self.born = now()
        self.tx = RelTx()
        self.rx = RelRx()
        self.fresh = True               # still owed a state snapshot
        self.since = 0                  # order of entering the room
        self.rx_pk = self.tx_pk = self.rx_by = self.tx_by = 0
        # kept by the room host only
        self.uuid = None
        self.welcome = None
        self.pub = None
        self.lan = []
        self.lport = 0
        self.want = 1
        self.auto_start = False         # told by the PC itself (1.0.8+); unknown counts as no


# ===========================================================================
# Mirroring of the shared page between PCs
# ===========================================================================
class Mirror:
    def __init__(self, eng):
        self.eng = eng
        self.page = eng.page
        pg = self.page
        self.g_known = bytes(pg.read(G_OFF, G_LEN))
        self.p_sent = 0
        self.p_remote = {}                              # node id -> bits that PC asserts
        self.p_union = 0
        self.ev_seq = {r: pg.u32(off) for r, (off, _) in EVENTS.items()}
        self.ev_queue = collections.deque()
        self.ev_next = {r: 0.0 for r in EVENTS}
        self.lanes = {}                                 # own slot -> lane content last sent
        self.js_seq = pg.u32(JS_SEQ)
        self.js_gen = 0
        self.js_out = None                              # sync this PC's game published
        self.js_in = None                               # sync applied here for a remote host
        self.last_sync = None

    # ---- state snapshot for a peer that just appeared ----------------------
    def snapshot_for(self, peer):
        eng = self.eng
        if not eng.is_player(peer):
            return
        eng.send_msg(peer, bytes([M_PAGE_P]) + self._local_bits().to_bytes(P_LEN, "little"))
        for s in eng.local_slots:                       # a newcomer needs the commands still on their way
            eng.send_msg(peer, bytes([M_LANE, s]) + bytes(self.page.read(LANE_OFF + s * LANE_LEN, LANE_LEN)))
        # The PC that has been in the room longest hands a newcomer the room's cheat flags.
        if eng.i_host_room():
            eng.send_msg(peer, bytes([M_PAGE_G]) + struct.pack("<H", 0) + bytes(self.page.read(G_OFF, G_LEN)))
            eng.send_plan(peer)
            eng.send_msg(peer, bytes([M_LIVE, 2 if eng.level_up is None else 1 if eng.level_up else 0]))
        eng.send_msg(peer, bytes([M_ROLE, 1 if eng.hosting() else 0]))
        if eng.i_host_room() and eng.chat:
            # the room's chat so far (kept in memory only, like the chat itself), for the newcomer's page
            log = [dict(n=n, t=x, w=int(w)) for _, w, n, x, _ in list(eng.chat)[-50:]]
            eng.send_msg(peer, bytes([M_CHATLOG]) + json.dumps(log).encode())
        eng.send_msg(peer, bytes([M_AUTO, 1 if eng.cfg.get("auto_start", True) else 0]))

    def _local_bits(self):
        return int.from_bytes(self.page.read(P_OFF, P_LEN), "little") & ~self.p_union

    def peer_gone(self, nid):
        self._apply_bits(nid, 0)
        self.p_remote.pop(nid, None)
        jo = self.js_out
        if jo:
            jo["targets"].discard(nid)

    def _apply_bits(self, nid, new):
        old = self.p_remote.get(nid, 0)
        others = 0
        for k, bits in self.p_remote.items():
            if k != nid:
                others |= bits
        setb = new & ~old
        clrb = old & ~new & ~others
        pg = self.page
        for i in range(P_LEN):
            sb, cb = (setb >> (8 * i)) & 0xFF, (clrb >> (8 * i)) & 0xFF
            if sb:
                pg.or8(P_OFF + i, sb)
            if cb:
                pg.and8(P_OFF + i, ~cb & 0xFF)
        self.p_remote[nid] = new
        self.p_union = others | new

    # ---- messages from other PCs -------------------------------------------
    def on_msg(self, peer, kind, body, t):
        pg = self.page
        if kind == M_PAGE_G and len(body) >= 2:
            off = struct.unpack_from("<H", body)[0]
            data = body[2:]
            if off + len(data) <= G_LEN and data:
                pg.write(G_OFF + off, data)
                g = bytearray(self.g_known)
                g[off:off + len(data)] = data
                self.g_known = bytes(g)
        elif kind == M_PAGE_P and len(body) == P_LEN:
            self._apply_bits(peer.id, int.from_bytes(body, "little"))
        elif kind == M_EVENT and len(body) > 1 and body[0] in EVENTS:
            off, ln = EVENTS[body[0]]
            if len(body) - 1 <= ln - 4:
                self.ev_queue.append((body[0], body[1:]))
        elif kind == M_LANE and len(body) == 1 + LANE_LEN:
            s = body[0]
            if s < NSLOTS and self.eng.slot_owner.get(s) == peer.id:      # a PC speaks only for its own slots
                off = LANE_OFF + s * LANE_LEN
                pg.write(off + 4, body[5:])             # the commands first, their count last
                pg.write(off, body[1:5])
        elif kind == M_JSYNC and len(body) > JS_HDR.size:
            self._jsync_in(peer, body, t)
        elif kind == M_JSYNC_PUB and len(body) >= 5:
            seq, status = struct.unpack_from("<IB", body)
            jo = self.js_out
            if jo and jo["seq"] == seq and peer.id in jo["targets"]:
                jo["pub"][peer.id] = t
                if status:
                    self.eng.log.warn("%s could not store the join save - check its game folder" % peer.name)
        elif kind == M_JSYNC_LOADED and len(body) >= 8:
            seq, total = struct.unpack_from("<II", body)
            jo = self.js_out
            if jo and jo["seq"] == seq and total < JS_FORCE:
                delta = total - jo["loaded"].get(peer.id, 0)
                if delta > 0:
                    jo["loaded"][peer.id] = total
                    if pg.u32(JS_SEQ) == seq:
                        pg.add_u32(JS_COUNT, delta)

    # ---- once per loop -------------------------------------------------------
    def poll(self, t):
        pg, eng = self.page, self.eng
        # global cheat flags: whichever side changed a byte last wins
        cur = pg.read(G_OFF, G_LEN)
        if cur != self.g_known:
            known = self.g_known
            lo = next(i for i in range(G_LEN) if cur[i] != known[i])
            hi = next(i for i in range(G_LEN - 1, -1, -1) if cur[i] != known[i])
            self.g_known = bytes(cur)
            eng.broadcast(bytes([M_PAGE_G]) + struct.pack("<H", lo) + bytes(cur[lo:hi + 1]))
        # command lanes of this PC's own games
        for s in eng.local_slots:
            lane = pg.read(LANE_OFF + s * LANE_LEN, LANE_LEN)
            if lane != self.lanes.get(s):
                first = s not in self.lanes
                self.lanes[s] = bytes(lane)
                if not first or any(lane):
                    eng.broadcast(bytes([M_LANE, s]) + bytes(lane))
        # per-player cheat bits: every PC owns the bits of its own players
        loc = self._local_bits()
        if loc != self.p_sent:
            self.p_sent = loc
            eng.broadcast(bytes([M_PAGE_P]) + loc.to_bytes(P_LEN, "little"))
        # teleport and drop relays written by a local game
        for r, (off, ln) in EVENTS.items():
            seq = pg.u32(off)
            if seq != self.ev_seq[r]:
                self.ev_seq[r] = seq
                eng.broadcast(bytes([M_EVENT, r]) + bytes(pg.read(off + 4, ln - 4)))
        # relays from other PCs, spaced out so a game polling once a frame sees each
        if self.ev_queue:
            r, data = self.ev_queue[0]
            if t >= self.ev_next[r]:
                self.ev_queue.popleft()
                off, _ = EVENTS[r]
                pg.write(off + 4, data)
                seq = (pg.u32(off) + 1) & 0xFFFFFFFF
                pg.set_u32(off, seq)
                self.ev_seq[r] = seq
                self.ev_next[r] = t + 0.06
        # join sync published by a local game (this PC hosts the campaign)
        seq = pg.u32(JS_SEQ)
        if seq != self.js_seq:
            self.js_seq = seq
            self._jsync_out(seq, t)
        jo = self.js_out
        if jo and not jo["done"]:
            self._jsync_watch(jo, t)
        ji = self.js_in
        if ji:
            cnt = pg.u32(JS_COUNT)
            if cnt != ji["reported"] and cnt < JS_FORCE and pg.u32(JS_SEQ) == ji["local_seq"]:
                ji["reported"] = cnt
                p = eng.peers.get(ji["origin"])
                if p:
                    eng.send_msg(p, bytes([M_JSYNC_LOADED]) + struct.pack("<II", ji["seq"], cnt))
            if t - ji["t0"] > 90:
                self.js_in = None

    # ---- this PC's game published a join sync ------------------------------
    def _jsync_out(self, seq, t):
        pg, eng = self.page, self.eng
        sender, nxt = pg.u32(JS_SENDER), pg.u32(JS_NEXT)
        raw = bytes(pg.read(JS_NAME, 64))
        name = raw.split(b"\0")[0].decode("ascii", "replace")
        targets = {n for n, q in eng.peers.items() if eng.is_player(q)}
        self.js_gen += 1
        self.js_in = None
        self.js_out = dict(seq=seq, t0=t, targets=targets, pub={}, loaded={}, sent=None, size=0,
                           raw=0, force_at=None, done=False, failed=False, name=name, gen=self.js_gen)
        if not targets:
            self.js_out["done"] = True
            return
        if not SAVE_NAME_RE.match(name):
            eng.log.error("Join sync uses save name %r, which cannot be sent to other PCs" % name)
            self.js_out.update(failed=True, force_at=t + 5.0)
            return
        if not eng.game_dir:
            eng.log.error("Join sync: no game folder set, so the save cannot be sent - other PCs will drop out")
            self.js_out.update(failed=True, force_at=t + 5.0)
            return
        path = os.path.join(eng.game_dir, "core", name + ".bin")
        level = 1 if len(targets) <= 3 else 6
        hdr = (seq, sender, nxt, raw)
        threading.Thread(target=self._read_worker, args=(self.js_gen, path, hdr, level), daemon=True).start()

    def _read_worker(self, gen, path, hdr, level):
        t0 = now()
        data, err = None, "not found"
        for _ in range(60):                      # the host writes the file before it publishes
            try:
                with open(path, "rb") as f:
                    data = f.read()
                if 0 < len(data) <= MAX_SAVE:
                    break
                err, data = "size %d" % len(data), None
            except OSError as e:
                err = str(e)
            time.sleep(0.025)
        if data is None:
            self.eng.post(("js_read_fail", gen, path, err))
            return
        comp = zlib.compress(data, level)
        self.eng.post(("js_ready", gen, hdr + (listed_tags(data),), len(data), zlib.crc32(data) & 0xFFFFFFFF, comp, now() - t0))

    def on_ready(self, gen, hdr, raw_len, crc, comp, secs, t):
        jo = self.js_out
        if not jo or jo["gen"] != gen or jo["done"]:
            return
        seq, sender, nxt, name, listed = hdr
        msg = bytes([M_JSYNC]) + JS_HDR.pack(seq, sender, nxt, raw_len, crc, name) + comp
        jo["sent"], jo["size"], jo["raw"] = t, len(comp), raw_len
        n = 0
        for nid in list(jo["targets"]):
            p = self.eng.peers.get(nid)
            if p:
                self.eng.send_msg(p, msg)
                n += 1
        self.eng.log.info("Join sync %d: sending %d KB (%.1f MB save, %s, packed in %d ms) to %d PC(s)"
                          % (seq, len(comp) // 1024, raw_len / 1048576.0, list_text(listed), secs * 1000, n))

    def on_read_fail(self, gen, path, err):
        jo = self.js_out
        if jo and jo["gen"] == gen:
            jo.update(failed=True, force_at=now() + 3.0)
            self.eng.log.error("Join sync: could not read %s (%s) - is the game folder right?" % (path, err))

    def _jsync_watch(self, jo, t):
        pg = self.page
        if pg.u32(JS_SEQ) != jo["seq"]:
            jo["done"] = True
            return
        waiting = [] if jo["failed"] else [n for n in jo["targets"] if n not in jo["pub"]]
        if jo["force_at"] is None and jo["sent"] is not None and not waiting:
            jo["force_at"] = t + 5.0             # every PC has the save: the game's own 5 s allowance
            took = t - jo["t0"]
            self.last_sync = dict(seq=jo["seq"], kb=jo["size"] // 1024, pcs=len(jo["targets"]),
                                  transfer_ms=int(took * 1000), when=time.time())
            self.eng.log.info("Join sync %d: every PC has the save after %d ms" % (jo["seq"], took * 1000))
        if (jo["force_at"] is not None and t >= jo["force_at"]) or t - jo["t0"] > 20.0:
            if waiting:
                names = ", ".join(self.eng.peers[n].name for n in waiting if n in self.eng.peers)
                self.eng.log.error("Join sync %d: no confirmation from %s after 20 s - releasing the host"
                                   % (jo["seq"], names or "some PCs"))
            # Ends the host's hold if a machine never reported; harmless if it already ended.
            pg.add_u32(JS_COUNT, JS_FORCE)
            jo["done"] = True

    # ---- a remote host published a join sync -------------------------------
    def _jsync_in(self, peer, body, t):
        seq, sender, nxt, raw_len, crc, raw_name = JS_HDR.unpack_from(body)
        name = raw_name.split(b"\0")[0].decode("ascii", "replace")
        eng = self.eng
        if not SAVE_NAME_RE.match(name) or raw_len > MAX_SAVE or not eng.game_dir:
            eng.log.error("Join sync from %s cannot be stored (%s)" % (
                peer.name, "no game folder set" if not eng.game_dir else "bad save name or size"))
            eng.send_msg(peer, bytes([M_JSYNC_PUB]) + struct.pack("<IB", seq, 1))
            return
        self.js_gen += 1
        hdr = (peer.id, seq, sender, nxt, raw_len, crc, raw_name, name)
        threading.Thread(target=self._write_worker, args=(self.js_gen, hdr, body[JS_HDR.size:], t), daemon=True).start()

    def _write_worker(self, gen, hdr, comp, t_rx):
        origin, seq, sender, nxt, raw_len, crc, raw_name, name = hdr
        try:
            d = zlib.decompressobj()
            data = d.decompress(comp, raw_len + 1)
            if len(data) != raw_len or (zlib.crc32(data) & 0xFFFFFFFF) != crc:
                raise ValueError("save damaged in transfer")
            folder = os.path.join(self.eng.game_dir, "core")
            os.makedirs(folder, exist_ok=True)
            path = os.path.join(folder, name + ".bin")
            tmp = path + ".h2link"
            with open(tmp, "wb") as f:
                f.write(data)
            for attempt in range(80):            # a game may still hold the previous save open
                try:
                    os.replace(tmp, path)
                    break
                except OSError:
                    if attempt == 79:
                        raise
                    time.sleep(0.025)
            self.eng.post(("js_written", gen, hdr + (listed_tags(data),), now() - t_rx))
        except Exception as e:
            self.eng.post(("js_write_fail", gen, hdr, str(e)))

    def on_written(self, gen, hdr, secs, t):
        origin, seq, sender, nxt, raw_len, crc, raw_name, name, listed = hdr
        eng, pg = self.eng, self.page
        peer = eng.peers.get(origin)
        if gen != self.js_gen or peer is None:
            return
        # Same order as the host: fields first, sequence number last.
        pg.set_u32(JS_SENDER, sender)
        pg.set_u32(JS_NEXT, nxt)
        pg.set_u32(JS_COUNT, 0)
        pg.write(JS_NAME, raw_name[:64].ljust(64, b"\0"))
        local = (pg.u32(JS_SEQ) + 1) & 0xFFFFFFFF
        pg.set_u32(JS_SEQ, local)
        self.js_seq = local
        self.js_in = dict(origin=origin, seq=seq, local_seq=local, reported=0, t0=t)
        eng.send_msg(peer, bytes([M_JSYNC_PUB]) + struct.pack("<IB", seq, 0))
        eng.log.info("Join sync %d from %s: save stored (%.1f MB, %s, %d ms), local game told to load"
                     % (seq, peer.name, raw_len / 1048576.0, list_text(listed), secs * 1000))

    def on_write_fail(self, gen, hdr, err):
        origin, seq = hdr[0], hdr[1]
        self.eng.log.error("Join sync %d: could not store the save (%s)" % (seq, err))
        peer = self.eng.peers.get(origin)
        if peer:
            self.eng.send_msg(peer, bytes([M_JSYNC_PUB]) + struct.pack("<IB", seq, 1))


# ===========================================================================
# Finding this PC's public address and asking the router to open the port
# ===========================================================================
STUN_SERVERS = (("stun.l.google.com", 19302), ("stun.cloudflare.com", 3478))
STUN_COOKIE = b"\x21\x12\xa4\x42"
SSDP_ADDR = ("239.255.255.250", 1900)


def stun_parse(data, txid):
    """Public (ip, port) from a STUN binding answer, or None."""
    if len(data) < 20 or data[:2] != b"\x01\x01" or data[4:8] != STUN_COOKIE or data[8:20] != txid:
        return None
    i, end, plain = 20, min(len(data), 20 + struct.unpack(">H", data[2:4])[0]), None
    while i + 4 <= end:
        typ, ln = struct.unpack(">HH", data[i:i + 4])
        v = data[i + 4:i + 4 + ln]
        if ln >= 8 and v[1] == 1:
            if typ == 0x0020:
                return (socket.inet_ntoa(bytes(a ^ b for a, b in zip(v[4:8], STUN_COOKIE))),
                        struct.unpack(">H", v[2:4])[0] ^ 0x2112)
            if typ == 0x0001:
                plain = (socket.inet_ntoa(v[4:8]), struct.unpack(">H", v[2:4])[0])
        i += 4 + ((ln + 3) & ~3)
    return plain


def private_ip(ip):
    """True for addresses that are not reachable from the internet."""
    try:
        a, b = [int(x) for x in ip.split(".")[:2]]
    except ValueError:
        return True
    return (a in (10, 127) or (a == 172 and 16 <= b <= 31) or (a == 192 and b == 168)
            or (a == 100 and 64 <= b <= 127) or (a == 169 and b == 254))


def _http(req):
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))   # the router is never behind a proxy
    try:
        with opener.open(req, timeout=4) as r:
            return 200, r.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode("utf-8", "replace")


def upnp_discover(bind_ip, target):
    """Ask the network for an internet gateway; return (control URL, service type) or None."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    locs = []
    try:
        try:
            s.bind((bind_ip, 0))
        except OSError:
            pass
        s.settimeout(0.4)
        for st in ("urn:schemas-upnp-org:device:InternetGatewayDevice:1",
                   "urn:schemas-upnp-org:service:WANIPConnection:1",
                   "urn:schemas-upnp-org:service:WANPPPConnection:1"):
            s.sendto(('M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\nMAN: "ssdp:discover"\r\nMX: 1\r\n'
                      'ST: %s\r\n\r\n' % st).encode(), target)
        end = time.time() + 2.5
        while time.time() < end:
            try:
                data, _ = s.recvfrom(4096)
            except socket.timeout:
                continue
            except OSError:
                break
            m = re.search(rb"(?im)^location:\s*(\S+)", data)
            if m and m.group(1).decode("ascii", "replace") not in locs:
                locs.append(m.group(1).decode("ascii", "replace"))
                end = min(end, time.time() + 0.6)
    finally:
        s.close()
    for loc in locs:
        try:
            code, xml = _http(urllib.request.Request(loc))
        except (OSError, ValueError):
            continue
        base = re.search(r"<URLBase>\s*([^<\s]+)", xml)
        for svc in re.findall(r"<service>(.*?)</service>", xml, re.S):
            typ = re.search(r"<serviceType>\s*([^<\s]+)", svc)
            ctl = re.search(r"<controlURL>\s*([^<\s]+)", svc)
            if typ and ctl and re.search(r"WAN(IP|PPP)Connection:[12]$", typ.group(1)):
                return urllib.parse.urljoin(base.group(1) if base else loc, ctl.group(1)), typ.group(1)
    return None


def upnp_call(control, service, action, args):
    body = ('<?xml version="1.0"?>\r\n<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" '
            's:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/"><s:Body><u:%s xmlns:u="%s">%s</u:%s>'
            '</s:Body></s:Envelope>' % (action, service, "".join("<%s>%s</%s>" % (k, v, k) for k, v in args), action))
    return _http(urllib.request.Request(control, data=body.encode(), headers={
        "Content-Type": 'text/xml; charset="utf-8"', "SOAPAction": '"%s#%s"' % (service, action)}))


def upnp_open(port, local_ip, bind_ip, target):
    """Forward UDP `port` on the router to this PC. Never raises."""
    out = dict(ok=False, ext_ip=None, why="no router answered", port=port)
    try:
        found = upnp_discover(bind_ip, target)
        if not found:
            return out
        control, service = found
        out.update(control=control, service=service)
        code, xml = upnp_call(control, service, "GetExternalIPAddress", [])
        m = re.search(r"<NewExternalIPAddress>\s*([0-9.]+)", xml)
        if m:
            out["ext_ip"] = m.group(1)
        for lease in (86400, 0):                 # some routers only take permanent entries
            code, xml = upnp_call(control, service, "AddPortMapping", [
                ("NewRemoteHost", ""), ("NewExternalPort", port), ("NewProtocol", "UDP"), ("NewInternalPort", port),
                ("NewInternalClient", local_ip), ("NewEnabled", 1), ("NewPortMappingDescription", APP),
                ("NewLeaseDuration", lease)])
            if code == 200:
                out["ok"] = True
                return out
        m = re.search(r"<errorDescription>\s*([^<]+)", xml)
        out["why"] = "the router refused: %s" % (m.group(1).strip() if m else "error %d" % code)
    except Exception as e:
        out["why"] = str(e) or e.__class__.__name__
    return out


def upnp_close(res):
    try:
        upnp_call(res["control"], res["service"], "DeletePortMapping",
                  [("NewRemoteHost", ""), ("NewExternalPort", res["port"]), ("NewProtocol", "UDP")])
    except Exception:
        pass


# ===========================================================================
# The engine: one thread owns every socket, the page and the room state
# ===========================================================================
def local_ips(target=None):
    ips = []
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect((target or "192.0.2.1", 9))
        ips.append(s.getsockname()[0])
        s.close()
    except OSError:
        pass
    try:
        for ip in socket.gethostbyname_ex(socket.gethostname())[2]:
            if ip not in ips:
                ips.append(ip)
    except OSError:
        pass
    return [ip for ip in ips if not ip.startswith("127.") and ip != "0.0.0.0"]


class Engine(threading.Thread):
    def __init__(self, cfg, cfg_path, log, opts):
        super().__init__(daemon=True)
        self.cfg, self.cfg_path, self.log, self.opts = cfg, cfg_path, log, opts
        self.plat = Platform(opts.page_file)
        self.loop_ip = opts.loop_ip or "127.0.0.1"
        # 0.0.0.0 so the game's discovery fan-out (sent to the broadcast address) arrives too
        self.slot_bind = opts.loop_ip or "0.0.0.0"
        self.wan_bind = opts.wan_bind or "0.0.0.0"
        self.cmds = queue.SimpleQueue()
        self.inbox = queue.SimpleQueue()
        self.sel = selectors.DefaultSelector()
        self.stop_flag = False
        self.snap = {}
        self.page_seen = now()          # last time a control page asked for the state
        self.launch_t = 0.0
        self.auto_tidy = None           # a launch whose ui_set_automation_ lines are still in init.txt
        self._prof, self._prof_next = "", 0.0
        self._launch_ver = 0
        self._first_window = True
        self.snapper = Snapper()
        self.update = None              # dict when a newer release is out (see _check_update)
        self._upd_next = now() + 5.0
        self._upd_busy = False
        self._window_no = 0
        self._launch_slot = -1
        self.uuid = bytes.fromhex(cfg["uuid"])
        self.sock = None
        self.page = None
        self.mirror = None
        self.slot_socks = {}
        self.mutexes = {}
        self.delayed = []
        self.room_gen = 0
        self.chat = collections.deque(maxlen=200)      # (number, time, name, text, from this PC)
        self.chat_seq = 0
        self.report = None
        self._exe_cache = {}
        self._clear_room()

    # ---- small helpers -------------------------------------------------------
    @property
    def game_dir(self):
        d = self.cfg.get("game_dir") or ""
        return d if d and os.path.isdir(d) else ""

    @property
    def in_room(self):
        return self.state in ("connected", "reconnecting")

    def post(self, item):
        self.inbox.put(item)

    def command(self, *item):
        self.cmds.put(item)

    def _clear_room(self):
        self.mode = "idle"
        self.state = "idle"
        self.error = None
        self.is_host = False
        self.my_id = None
        self.key = b""
        self.epoch = 0
        self.peers = {}
        self.slot_owner = {}
        self.local_slots = []
        self.local_set = frozenset()
        self.conflicts = []
        self.games = 0
        self.room_name = ""
        self.host_addr = None
        self.host_text = ""
        self.my_pub = None
        self.pwkey = b""
        self.hs_state = None
        self.pending = {}
        self.by_uuid = {}
        self.reserved = {}
        self.stray = 0
        self.lan_ips = []
        self.room_gen += 1              # answers from helper threads of an earlier room are dropped
        self.pub_ip = None
        self.stun_addrs, self.stun_txid, self.stun_tries, self.stun_next = [], None, 0, 0.0
        self.upnp = None
        self.reach_warned = False
        self.relay_only = False         # the server hands out no addresses; everything goes through it
        self.server_room = False        # the room lives on a lobby server
        self.room_req = ""
        self.plan = clean_plan(self.cfg.get("plan") or {}) or clean_plan({})
        if self.plan["level"] not in dict(LEVELS):          # saved from when the training levels were offered
            self.plan["level"] = LEVELS[0][0]
        self.plan_known = False
        # The room host says when its level has finished loading. A game that joins while the host is
        # still loading is let in by the game's own start-together path, with no player of its own.
        self.level_up = False           # room host: my level is loaded
        self.level_tail = None          # [log path, read position, state, since]
        self.level_since = None         # when this PC's game was first seen running
        self.level_scan = 0.0
        self.host_live = None           # others: None = host never said (older H2Link), else True/False
        self.live_from = None           # which room host that came from
        self.was_host = False
        self.hosting_sent = False
        self.launch_wait = False
        self.go_more, self.go_next = 0, 0.0      # further windows to start after the room host's launch
        self.go_poll = 0.0
        self.host_lobby = False                  # the room host launched; its game is in its lobby, not a level
        self.since = 0
        self.admitted = 0
        self.next_fast = self.next_slow = self.next_snap = 0.0

    def save_cfg(self):
        try:
            with open(self.cfg_path, "w") as f:
                json.dump(self.cfg, f, indent=1)
        except OSError as e:
            self.log.warn("Could not save settings to %s (%s)" % (self.cfg_path, e))

    # ---- sockets, mutexes -----------------------------------------------------
    def _open_wan(self, port, fallback):
        self._close_wan()
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            s.bind((self.wan_bind, port))
        except OSError as e:
            if not fallback:
                s.close()
                raise
            self.log.warn("UDP port %d is busy (%s) - using a free port instead" % (port, e))
            s.bind((self.wan_bind, 0))
        s.setblocking(False)
        for opt in (socket.SO_RCVBUF, socket.SO_SNDBUF):
            try:
                s.setsockopt(socket.SOL_SOCKET, opt, 4 << 20)
            except OSError:
                pass
        Platform.no_connreset(None, s)
        self.sel.register(s, selectors.EVENT_READ, None)
        self.sock = s
        self.wan_port = s.getsockname()[1]

    def _close_wan(self):
        if self.sock:
            try:
                self.sel.unregister(self.sock)
            except Exception:
                pass
            self.sock.close()
            self.sock = None

    def _release(self):
        for s in self.slot_socks.values():
            try:
                self.sel.unregister(s)
            except Exception:
                pass
            s.close()
        self.slot_socks = {}
        for slot, h in self.mutexes.items():
            self.plat.release_mutex(slot, h)
        self.mutexes = {}
        self.conflicts = []

    def _claim(self, slots):
        """Take every slot that is not ours: hold its mutex, listen on its ports."""
        self._release()
        self.local_slots = sorted(slots)
        self.local_set = frozenset(slots)
        for slot in range(NSLOTS):
            if slot in self.local_set:
                continue
            self.mutexes[slot] = self.plat.claim_mutex(slot)
            for pidx, base in enumerate(BASE_PORTS):
                port = base + slot * SPACING
                s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                try:
                    s.bind((self.slot_bind, port))
                except OSError as e:
                    s.close()
                    if pidx < 2:
                        denied = getattr(e, "winerror", None) == 10013
                        self.conflicts.append((slot, port, denied))
                    continue
                s.setblocking(False)
                try:
                    s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1 << 20)
                except OSError:
                    pass
                Platform.no_connreset(None, s)
                self.sel.register(s, selectors.EVENT_READ, (slot, pidx))
                self.slot_socks[(slot, pidx)] = s
        busy = sorted({"%02d" % (c[0] + 1) for c in self.conflicts if not c[2]})
        denied = sorted({str(c[1]) for c in self.conflicts if c[2]})
        if busy:
            self.log.error("Ports of slot %s are in use on this PC. A game started before joining is probably "
                           "sitting in another player's slot: close every game window, then start the game "
                           "again." % ", ".join(busy))
        if denied:
            self.log.error("Windows refuses UDP port %s (reserved; see 'netsh int ipv4 show excludedportrange "
                           "udp'). The player in that slot cannot be reached from this PC." % ", ".join(denied))
        if self.page is None:
            self.page = Page(self.plat)
            self.mirror = Mirror(self)
        self.log.info("This PC plays in slot %s; the other %d slots are held for the room"
                      % (slot_text(self.local_slots), NSLOTS - len(self.local_slots)))

    def _running_slots(self):
        """Slots whose mutex exists right now = game instances already running."""
        first = [s for s in range(NSLOTS) if self.plat.mutex_exists(s)]
        if not first:
            return []
        time.sleep(0.04)                 # a game's discovery fan-out touches every mutex for an instant
        return [s for s in first if self.plat.mutex_exists(s)]

    def _wan_send(self, pkt, addr):
        o = self.opts
        if o.sim_loss and random.random() < o.sim_loss:
            return True
        if o.sim_delay:
            self.delayed.append((now() + o.sim_delay / 1000.0, pkt, addr))
            return True
        try:
            self.sock.sendto(pkt, addr)
            return True
        except (BlockingIOError, InterruptedError):
            return False
        except OSError:
            return True

    def route(self, p, t):
        if p.addr is not None and (self.is_host or p.id == 0 or t - p.last_rx < DIRECT_TIMEOUT):
            return p.addr
        return None if self.is_host else self.host_addr      # relayed by the room host

    def _send_peer(self, p, pkt, t):
        a = self.route(p, t)
        return self._wan_send(pkt, a) if a else True

    def send_msg(self, p, msg):
        if len(p.tx.queue) > 80000:
            self.log.error("Too much unsent data for %s - dropping it" % p.name)
            p.tx.reset()
        p.tx.enqueue(msg)

    def broadcast(self, msg):
        for p in self.peers.values():
            if self.is_host or self.is_player(p):
                self.send_msg(p, msg)

    def is_player(self, p):
        """False for the lobby server, which sits in the room as node 0 without a game."""
        return not (self.server_room and p.id == 0)

    # ---- room host and the level plan --------------------------------------------
    def hosting(self):
        """This PC started its game as the room's host and that game is still running."""
        return bool(self.games) and self.cfg.get("launched_as") == "host"

    def room_host(self):
        """Who decides for the room: the PC whose game hosts, else whoever has been in the room longest.
        None if that is this PC, else the peer."""
        cands = [(not q.hosting, q.since, q) for q in self.peers.values() if self.is_player(q)]
        cands.append((not self.hosting(), self.since, None))
        return min(cands, key=lambda c: (c[0], c[1]))[2]

    def i_host_room(self):
        return self.in_room and self.room_host() is None

    def send_plan(self, peer=None):
        msg = bytes([M_ROOM]) + json.dumps(self.plan).encode()
        if peer is None:
            self.broadcast(msg)
        else:
            self.send_msg(peer, msg)

    def _cmd_roomset(self, d):
        if not self.i_host_room():
            return
        if not str(d.get("level", "x")).strip():
            d = {k: v for k, v in d.items() if k != "level"}     # the list had no entry for the level in use
        plan = clean_plan(d, self.plan)
        if plan and plan["level"] not in dict(LEVELS):          # a training level set by an older room host
            plan["level"] = LEVELS[0][0]
        if plan and plan != self.plan:
            self.plan = self.cfg["plan"] = plan
            self.save_cfg()
            self.send_plan()
            self.log.info("Room set to %s" % plan_text(plan))

    def session_name(self):
        """Name of the in-game session every PC of this room creates or looks for."""
        slug = re.sub(r"[^a-z0-9]+", "_", self.room_name.lower()).strip("_")[:24]
        return "h2l_" + (slug or "room")

    def _exe_info(self, exe):
        """(build number from the exe's JIPvNN tag, tick rate it runs at); (0, 0) if it is not a sysnet build."""
        try:
            key = (os.path.getmtime(exe), os.path.getsize(exe))
            hit = self._exe_cache.get(exe)
            if not hit or hit[0] != key:
                with open(exe, "rb") as f:
                    data = f.read()
                m = re.search(rb"JIPv(\d+)", data)
                tick = data[TICK_BYTE] if len(data) > TICK_BYTE and data[TICK_BYTE - 1] == 0x6A else 0
                hit = self._exe_cache[exe] = (key, (int(m.group(1)) if m else 0, tick if tick in TICK_NAME else 0))
            return hit[1]
        except OSError:
            return 0, 0

    def _write_init(self, role):
        """Write the game's init.txt: the player's own lines, the fixed lines, and for a launch
        from a room the automation lines. role: 'host', 'join' or None."""
        d = self.game_dir
        if not d:
            return
        path, mine = os.path.join(d, "init.txt"), os.path.join(d, "init_user.txt")
        digest = lambda text: hashlib.sha1(text.encode("utf-8", "replace")).hexdigest()
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                cur = f.read()
            if digest(cur) != self.cfg.get("init_hash"):        # not written by H2Link: the player's own file
                with open(mine, "w", encoding="utf-8") as f:
                    f.write(cur)
        except OSError:
            pass
        lines = []
        role = role if role in ("host", "join") else None
        try:
            with open(mine, encoding="utf-8", errors="replace") as f:
                for ln in f:
                    ln = ln.strip()
                    if ln and not ln.lower().startswith(INIT_OURS) and ln not in lines:
                        lines.append(ln)
        except OSError:
            pass
        lines += INIT_ALWAYS
        if role:
            # Everyone in the room runs with the room host's choices, or the games drift apart.
            lines += INIT_CHEATS_ON if self.plan["cheats"] else INIT_CHEATS_OFF
            lines += ["debug_ice_cream_flavor_status_%s on" % k for k in self.plan["skulls"]]
            lines.append("ui_set_automation_desired_network_session_name %s" % self.session_name())
            if role == "host":
                lines.append("ui_set_automation_variant_type_and_map %d %d" % (11 + self.plan["diff"], self.plan["level"]))
            room = self.launch_count()
            if True:                                # (always: the "Choose a player" screen is never shown)
                # No "Choose a player" screen. Exe v43+: the profile line only stores the name; when the
                # two counts make the game sign controller 1 in, it looks that name up among the saved
                # profiles (ignoring case: the console passes it in lower case) and falls back to the guest
                # profile if none matches. Older exes act on the name at once, before the saved profiles
                # can be read, and make a new profile - so the line is only written for v43+.
                # Only this PC's first game window signs in with the profile; any further window would sign
                # in as the same player, so it signs in as a guest instead. Exe v71+ names that guest after
                # the name given here when no saved profile has it ("Guest (1)", "Guest (2)" ...), without
                # creating a profile; older exes get no line and use the plain guest profile.
                prof = self.cfg.get("profile") if self._first_window else ""
                known = saved_profiles()
                if prof and known is not None and prof.lower() not in known:
                    # no Halo 2 profile of that name on this PC: this window plays under its H2Link name,
                    # the guest path every further window takes
                    self.log.info("No Halo 2 profile named \"%s\" on this PC - you play as %s" % (
                        prof, self.slot_names().get(self._launch_slot, window_name(self.cfg.get("name", ""), 0))))
                    prof = ""
                if prof and self._launch_ver >= 43:
                    lines.append('ui_set_automation_desired_controller_player_profile 0 "%s" ""' % prof)
                elif self._launch_ver >= 71:
                    # No saved profile for this window: it signs in as a guest named as the room shows it
                    # ("Name", "Name (1)" ...). Every player's name must differ: the game stops when two
                    # players in one lobby have the same one.
                    lines.append('ui_set_automation_desired_controller_player_profile 0 "%s" ""'
                                 % self.slot_names().get(self._launch_slot,
                                                         window_name(self.cfg.get("name", ""), self._window_no)))
                lines.append("ui_set_automation_desired_local_user_count 1")
                # (sic) the lobby refuses to go on if the local count is above this one, which starts at 0
                if role != "host":
                    lines.append("ui_set_automation_desired_desired_network_game_player_count 1")
            if role == "host":
                # The game's own lobby automation starts the level only once this many players are in its
                # lobby ("not enough network players to start the game" until then): every window in the
                # room, whose games H2Link starts at the same time. So everyone loads the level together.
                lines.append("ui_set_automation_desired_desired_network_game_player_count %d" % max(1, room))
            lines.append("ui_set_automation_mode system_link_auto_%s" % role)
        else:
            lines += INIT_CHEATS_ON
        text = "\n".join(lines) + "\n"
        with open(path, "w", encoding="utf-8", newline="\r\n") as f:
            f.write(text)
        self.cfg["init_hash"] = digest(text)
        self.save_cfg()

    # ---- commands from the UI ------------------------------------------------
    def _apply_settings(self, d):
        c = self.cfg
        for k in ("name", "game_dir", "exe", "args", "password", "address", "server", "room"):
            if k in d and isinstance(d[k], str):
                if k == "server" and not d[k].strip() and read_server_key(c.get("server", "")):
                    continue
                c[k] = d[k].strip()
        if "skip_picker" in d:
            c["skip_picker"] = bool(d["skip_picker"])
        if "snap_windows" in d:
            c["snap_windows"] = bool(d["snap_windows"])
        if "auto_start" in d:
            c["auto_start"] = bool(d["auto_start"])
            if self.in_room:
                self.broadcast(bytes([M_AUTO, 1 if c["auto_start"] else 0]))
        if isinstance(d.get("profile"), str):
            # a Halo 2 profile name: 16 characters at most, and it goes into a quoted console argument
            c["profile"] = re.sub(r'["\\\x00-\x1f]', "", d["profile"]).strip()[:16]
        for k, lo, hi in (("port", 1, 65535), ("want", 1, MAX_WINDOWS)):
            if k in d:
                try:
                    c[k] = min(hi, max(lo, int(d[k])))
                except (TypeError, ValueError):
                    pass
        c["name"] = (c.get("name") or "Player")[:24]
        self.save_cfg()

    def _cmd_host(self, d):
        if self.mode != "idle":
            self._leave()
        self._apply_settings(d)
        c = self.cfg
        # The usual port may be taken on this PC, by the lobby server for instance: then the next free one.
        # Players type the address with ":port" then; the page shows it that way.
        err = None
        for port in range(c["port"], c["port"] + 10):
            try:
                self._open_wan(port, False)
                break
            except OSError as e:
                err = err or e
        else:
            self.error = ("UDP ports %d to %d are all in use on this PC, so it cannot host. (%s)"
                          % (c["port"], c["port"] + 9, err))
            self.log.error(self.error)
            return
        if self.wan_port != c["port"]:
            self.log.warn("UDP port %d is in use on this PC (the lobby server, or another copy of %s) - hosting on "
                          "port %d instead. Players join with the address shown, port included."
                          % (c["port"], APP, self.wan_port))
        self.mode, self.state, self.is_host, self.error = "host", "connected", True, None
        self.my_id = 0
        self.key = os.urandom(4)
        self.epoch = random.getrandbits(32) | 1
        self.pwkey = room_key_of(c.get("password"))
        self.room_name = "%s's room" % c["name"]
        self.lan_ips = local_ips()
        running = self._running_slots()
        self._over_limit(running)
        want = min(MAX_WINDOWS, max(c.get("want", 1), len(running)))
        slots = self._alloc(want, running[:MAX_WINDOWS], self.uuid)
        self._claim(slots)
        self.save_cfg()
        self._rebuild_owner()
        self.log.info("Room open on UDP port %d" % self.wan_port)
        self._net_start(None)

    def _over_limit(self, running):
        if len(running) > MAX_WINDOWS:
            self.log.warn("%d game windows are open on this PC; only %d can take part. Slots %s stay out of "
                          "the room - close those windows." % (len(running), MAX_WINDOWS,
                          ", ".join("%02d" % (s + 1) for s in running[MAX_WINDOWS:])))

    def _cmd_join(self, d):
        if self.mode != "idle":
            self._leave()
        self._apply_settings(d)
        c = self.cfg
        via = d.get("via") == "server"
        text = c.get("server", "") if via else c.get("address", "")
        room = clean_room(c.get("room", "")) if via else ""
        if via and not room:
            self.error = "Type a room name, or pick a room from the list."
            return
        hidden = via and text.strip().upper().startswith(KEY_PREFIX)
        try:
            host, port, hidden = server_target(text) if via else split_addr(text) + (False,)
        except ValueError:
            self.error = (KEY_DAMAGED if hidden else
                          "\"%s\" is not an address %s can use. Use an IP or name, like 203.0.113.7:%d." % (text, APP, DEFAULT_PORT))
            self.log.error(self.error)
            return
        try:
            ip = socket.gethostbyname(host)
        except OSError:
            self.error = KEY_NO_NAME if hidden else "The name \"%s\" cannot be looked up from this PC." % host
            self.log.error(self.error)
            return
        try:
            self._open_wan(c["port"], True)
        except OSError as e:
            self.error = "No UDP port could be opened (%s)" % e
            return
        self.mode, self.state, self.is_host, self.error = "client", "connecting", False, None
        self.host_addr = (ip, port)
        self.host_text = "" if hidden else "%s:%d" % (host, port)
        self.pwkey = room_key_of(c.get("password"))
        self.room_req, self.server_room = room, via
        self._hs_begin(now())
        self.log.info("Contacting the server" if hidden else
                      "Contacting the %s at %s" % ("server" if via else "room host", self.host_text))

    # ---- public address and router port ------------------------------------------
    def _net_start(self, host_ip):
        stun, ssdp = os.environ.get("H2LINK_STUN"), os.environ.get("H2LINK_SSDP")
        if self.opts.wan_bind and not (stun or ssdp):
            return                      # simulated PCs on loopback: nothing to look up
        threading.Thread(target=self._net_worker, args=(self.room_gen, self.wan_port, host_ip, stun, ssdp),
                         daemon=True).start()

    def _net_worker(self, gen, port, host_ip, stun, ssdp):
        def pair(text):
            h, _, p = text.rpartition(":")
            return h, int(p)
        addrs = []
        for h, p in ([pair(stun)] if stun else STUN_SERVERS):
            try:
                addrs.append((socket.gethostbyname(h), p))
            except OSError:
                pass
        self.post(("stun_addrs", gen, addrs))
        ips = local_ips(host_ip)
        lip = ips[0] if ips else ""
        res = upnp_open(port, lip, "" if ssdp else lip, pair(ssdp) if ssdp else SSDP_ADDR)
        self.post(("upnp", gen, res))

    def _on_net(self, item, t):
        if item[1] != self.room_gen or not self.in_room:
            if item[0] == "upnp" and item[2].get("ok"):
                threading.Thread(target=upnp_close, args=(item[2],), daemon=True).start()
            return
        if item[0] == "stun_addrs":
            self.stun_addrs, self.stun_txid, self.stun_tries, self.stun_next = item[2], os.urandom(12), 0, 0.0
            return
        res = self.upnp = item[2]
        port = res["port"]
        if res["ok"]:
            self.log.info("The router opened UDP port %d for this PC" % port)
        elif self.is_host:
            self.log.warn("The router did not open UDP port %d by itself (%s). Forward it to this PC by hand, "
                          "or players outside your network cannot join." % (port, res["why"]))
        self._check_reach()

    def _check_reach(self):
        """Say so when this PC sits behind a second router or a provider-side NAT."""
        ext = self.upnp.get("ext_ip") if self.upnp else None
        if not self.is_host or not ext or self.reach_warned:
            return
        if private_ip(ext) or (self.pub_ip and self.pub_ip != ext):
            self.reach_warned = True
            self.log.warn("This PC is behind two routers or a provider-side NAT (router reports %s%s). Players "
                          "outside may not reach it even with the port open; another player may have to host."
                          % (ext, ", internet sees %s" % self.pub_ip if self.pub_ip else ""))

    def _chat_add(self, name, text, mine):
        self.chat_seq += 1
        self.chat.append((self.chat_seq, time.time(), name, text, mine))

    def _cmd_chat(self, d):
        text = " ".join(str(d.get("text", "")).split())[:300]
        if not text or not self.in_room:
            return
        self.broadcast(bytes([M_CHAT]) + json.dumps(dict(text=text)).encode())
        self._chat_add(self.cfg.get("name", "?"), text, True)

    def _leave(self):
        self.chat.clear()
        if self.mode == "idle":
            return
        if self.upnp and self.upnp.get("ok"):
            threading.Thread(target=upnp_close, args=(self.upnp,), daemon=True).start()
        if self.sock and self.key:
            for p in list(self.peers.values()):
                a = self.route(p, now())
                if a:
                    for _ in range(2):
                        self._wan_send(HDR.pack(T_BYE, self.my_id, p.id, self.key), a)
        self.auto_tidy = None
        if self.cfg.get("init_hash"):
            try:
                self._write_init(None)          # a game started later without H2Link must not auto-join
            except OSError:
                pass
        self._release()
        self._close_wan()
        if self.page:
            self.page.close()
        self.page = self.mirror = None
        was = self.mode
        self._clear_room()
        self.log.info("Room closed" if was == "host" else "Left the room")

    def _find_exe(self, tick=None):
        """The exe to launch. With a tick rate, the newest sysnet build in the folder that runs at it."""
        d = self.game_dir
        if not d:
            return None
        name = self.cfg.get("exe")
        if name:
            p = name if os.path.isabs(name) else os.path.join(d, name)
            return p if os.path.isfile(p) else None
        found = glob.glob(os.path.join(d, "halo2_sysnet_auto16*.exe"))
        if tick:
            found = [f for f in found if self._exe_info(f)[1] == tick]
        if found:
            return max(found, key=lambda f: (self._exe_info(f)[0], os.path.getmtime(f)))
        if tick:
            return None
        p = os.path.join(d, "halo2.exe")
        return p if os.path.isfile(p) else None

    def slot_names(self):
        """{slot: name} for every game window in the room, the same on every PC: each PC's windows are
        "Name", "Name (1)", "Name (2)" ... and, going by slot number, a name already taken gets the next free
        number."""
        rows = [(s, self.cfg.get("name", ""), k) for k, s in enumerate(sorted(self.local_slots))]
        for p in self.peers.values():
            if self.is_player(p):
                rows += [(s, p.name, k) for k, s in enumerate(sorted(p.slots))]
        names, used = {}, set()
        for s, base, k in sorted(rows):
            n = k
            name = window_name(base, n)
            while name.lower() in used:
                n += 1
                name = window_name(base, n)
            used.add(name.lower())
            names[s] = name
        return names

    def launch_count(self):
        """Game windows that start with the room host's launch: this PC's, and those of every PC whose
        "Start my game when the room host launches" is on. The host's lobby and its first level wait for
        these; PCs that start by hand later join the game in progress instead, so nothing waits for them."""
        return len(self.local_slots) + sum(len(p.slots) for p in self.peers.values()
                                           if self.is_player(p) and p.auto_start)

    def _cmd_launch(self, d):
        if not self.in_room:
            self.log.warn("Enter a room first - the game picks its slot when it starts")
            return
        if not self.i_host_room() and not self.plan_known:
            self.log.warn("Still waiting for the room host's settings - try again in a moment")
            return
        tick = self.plan["tick"]
        exe = self._find_exe(tick)
        if not exe:
            if self._find_exe():
                self.log.error("The room plays at %s, but the game folder has no %d-tick exe. Put "
                               "halo2_sysnet_auto16_v%d_%dtick.exe (or newer) in it." % (TICK_NAME[tick], tick, AUTO_EXE, tick))
            else:
                self.log.error("No game exe found. Set the game folder (and the exe name if it is unusual).")
            return
        free = [s for s in self.local_slots if not self.plat.mutex_exists(s)]
        self._first_window = len(free) == len(self.local_slots)     # no game of this PC is running yet
        mine = sorted(self.local_slots)
        self._window_no = mine.index(free[0]) if free and free[0] in mine else 0   # which of this PC's windows
        self._launch_slot = free[0] if free else -1
        if not free:
            self.log.warn("Every slot of this PC already has a game running")
            return
        ver, exe_tick = self._exe_info(exe)
        self._launch_ver = ver
        role, what = None, "it takes slot %s" % slot_text(free[:1])
        if ver >= AUTO_EXE:
            # The room host's first window opens the game; every other window joins it.
            role = "host" if self.i_host_room() and len(free) == len(self.local_slots) else "join"
            if role == "join" and self.host_lobby and not d.get("now"):
                d = dict(d, now=True, go=True)               # the host waits in its lobby: join it now
            if role == "join" and self.host_live is False and not d.get("now"):
                if not self.launch_wait:
                    self.launch_wait = True
                    self.log.info("Waiting for the host's level to finish loading. The game starts by itself then; "
                                  "press the button again to start it now anyway.")
                    return
                if not d.get("go"):
                    self.log.warn("Starting now although the host's level is not loaded yet")
            self.launch_wait = False
            what = ("it opens the room's game: %s" % plan_text(self.plan) if role == "host"
                    else "it joins the room's game by itself")
        else:
            self.log.warn("%s is older than v%d, so nothing is set up automatically. Use the game's menus."
                          % (os.path.basename(exe), AUTO_EXE))
        if exe_tick and exe_tick != tick:
            self.log.warn("%s runs at %d tick but the room is set to %d. Every PC must use the same."
                          % (os.path.basename(exe), exe_tick, tick))
        try:
            self._write_init(role)
        except OSError as e:
            self.log.warn("Could not write init.txt in the game folder (%s) - use the game's menus" % e)
        if role == "host" and self.page:
            # every window in the room: the host's game waits at its first level until they have all joined
            n = self.launch_count()
            self.page.set_u32(EXPECT_OFF, n if ver >= 70 else 0)
        try:
            args = shlex.split(self.cfg.get("args", ""), posix=False)
            proc = subprocess.Popen([exe] + args, cwd=self.game_dir, env=clean_env())
            if self.cfg.get("snap_windows", True):
                # split screen: this window's place among this PC's windows
                self.snapper.add(proc.pid, self._window_no, len(self.local_slots))
            self.log.info("Started %s: %s" % (os.path.basename(exe), what))
            if role == "host":
                self.broadcast(bytes([M_GO]))           # the other PCs start their games too
                if len(free) > 1:
                    # This PC's further windows join the host's lobby too, one after another (each reads
                    # init.txt as it starts), as a client PC's windows do on the room host's launch.
                    self.go_more, self.go_next = len(free) - 1, now() + GO_SPACING
            self.cfg["launched_as"], self.launch_t = role or "", now()
            self.launch_wall = time.time()              # for comparing with the game's log file times
            self.save_cfg()
            # The game reads init.txt once, at start. When this one has loaded its level the automation
            # lines have done their job and come out, so a game started later by hand does not auto-join.
            # A later launch replaces this entry, so its own lines are never taken out from under it.
            self.auto_tidy = (dict(t=now(), wall=time.time(), before=set(self.local_slots) - set(free), scan=0.0)
                              if role else None)
        except OSError as e:
            self.log.error("Could not start %s (%s)" % (exe, e))

    def _strip_automation(self):
        """Take the ui_set_automation_ lines out of init.txt, leaving everything else as it is."""
        self.auto_tidy = None
        d = self.game_dir
        if not d:
            return
        path = os.path.join(d, "init.txt")
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                cur = f.read()
        except OSError:
            return
        if hashlib.sha1(cur.encode("utf-8", "replace")).hexdigest() != self.cfg.get("init_hash"):
            return                              # changed since H2Link wrote it: the player's file now
        lines = [ln for ln in cur.splitlines() if ln.strip() and not ln.strip().lower().startswith("ui_set_automation_")]
        text = "\n".join(lines) + "\n"
        try:
            with open(path, "w", encoding="utf-8", newline="\r\n") as f:
                f.write(text)
        except OSError as e:
            self.log.warn("Could not tidy init.txt (%s)" % e)
            return
        # the hash is of the text before newline translation, the same way _write_init stores it
        self.cfg["init_hash"] = hashlib.sha1(text.encode("utf-8", "replace")).hexdigest()
        self.save_cfg()
        self.log.info("The game is in - automation lines taken out of init.txt")

    def _tidy_poll(self, t):
        """After a launch: once the new game has loaded a level, its automation lines are no longer needed."""
        a = self.auto_tidy
        if a is None or t < a["scan"]:
            return
        a["scan"] = t + 2.0
        new = [s for s in self.local_slots if self.games >> s & 1 and s not in a["before"]]
        if not new:
            if t - a["t"] > 60.0:               # it never came up, or already closed: nothing will read the lines now
                self._strip_automation()
            return
        if t - a["t"] > 240.0:                  # long past the start, whatever its log says
            return self._strip_automation()
        for slot in new:
            try:
                logs = [f for f in self._game_logs(slot) if os.path.basename(f).lower().startswith("networking_debug_")
                        and os.path.getmtime(f) >= a["wall"] - 5]
            except OSError:
                continue
            for f in logs[:1]:
                try:
                    with open(f, "rb") as fh:
                        fh.seek(max(0, os.path.getsize(f) - (1 << 20)))
                        chunk = fh.read()
                except OSError:
                    continue
                for line in chunk.split(b"\n"):
                    if b"lifecycle: MAP-LOADED " in line and b"\\ui\\mainmenu" not in line.lower():
                        return self._strip_automation()

    def _window_read_init(self, slot, since):
        """True once the game started in this slot at `since` has read init.txt: its debug log then shows the
        automation mode being set. Until then a further window must not start (init.txt is rewritten for it)."""
        if slot is None or slot < 0 or not self.game_dir:
            return False
        try:
            for path in self._game_logs(slot):
                if os.path.basename(path).lower().startswith("debug_full") and os.path.getmtime(path) >= since - 1:
                    with open(path, "rb") as fh:
                        fh.seek(max(0, os.path.getsize(path) - 65536))
                        tail = fh.read()
                    i = tail.rfind(b"blam  debug pc")          # this run's start
                    return i >= 0 and b"Setting automation mode from" in tail[i:]
        except OSError:
            pass
        return False

    def _game_logs(self, slot):
        """The game's log files of one slot: the newest networking log and the cumulative debug log."""
        net, full = [], []
        root = self.game_dir
        depth0 = root.rstrip("\\/").count(os.sep)
        for d, dirs, files in os.walk(root):
            if d.count(os.sep) - depth0 >= 2:
                dirs[:] = []
            for f in files:
                low = f.lower()
                if low == "debug_full_s%02d.txt" % slot:
                    full.append(os.path.join(d, f))
                elif low.startswith("networking_debug_") and low.endswith("_s%02d.txt" % slot):
                    net.append(os.path.join(d, f))
        net.sort(key=os.path.getmtime, reverse=True)
        return net[:2] + full[:1]

    @staticmethod
    def _vtuple(v):
        try:
            return tuple(int(x) for x in re.findall(r"\d+", str(v))[:4])
        except ValueError:
            return ()

    def _local_exe_version(self):
        best = 0
        try:
            for ex in (self._find_exe(30), self._find_exe(60), self._find_exe()):
                if ex:
                    best = max(best, self._exe_info(ex)[0] or 0)
        except Exception:
            pass
        return best

    def _http_json(self, url, timeout=8):
        req = urllib.request.Request(url, headers={"User-Agent": "H2Link/" + VERSION,
                                                   "Accept": "application/vnd.github+json"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read(1 << 20).decode("utf-8", "replace"))

    def _check_update(self):
        """In the background: the newest release on GitHub, compared with this H2Link and the game exe here."""
        try:
            repo = str(self.cfg.get("update_repo") or UPDATE_REPO).strip()
            if not re.fullmatch(r"[\w.-]+/[\w.-]+", repo):
                return                                     # not set (a build without a repository)
            api = str(self.cfg.get("update_api") or "https://api.github.com").rstrip("/")
            rel = self._http_json("%s/repos/%s/releases/latest" % (api, repo))
            assets = {a.get("name", ""): a.get("browser_download_url", "") for a in rel.get("assets", [])}
            man = {}
            if assets.get("manifest.json"):
                man = self._http_json(assets["manifest.json"])
            app_v = str(man.get("h2link") or rel.get("tag_name", "")).lstrip("vV")
            exe_v = int(man.get("exe") or 0)
            newer_app = self._vtuple(app_v) > self._vtuple(VERSION)
            newer_exe = exe_v > self._local_exe_version() > 0
            if newer_app or newer_exe:
                self.update = dict(version=app_v, exe=exe_v, newer_app=newer_app, newer_exe=newer_exe,
                                   page=rel.get("html_url", "https://github.com/%s/releases" % repo),
                                   installer=assets.get(man.get("installer") or "H2Link_Setup.exe", ""))
                if not getattr(self, "_upd_said", False):
                    self._upd_said = True
                    self.log.info("An update is out: H2Link %s%s - see the top of this page" % (
                        app_v, ", game exe v%d" % exe_v if exe_v else ""))
            else:
                self.update = None
        except Exception:
            pass                                           # offline, rate-limited, no release yet: try later
        finally:
            self._upd_busy = False

    def _cmd_update(self, d):
        """Download the new release's installer in the background, then close H2Link: the installer runs
        without any window (it remembers the game folder) and starts H2Link again when it is done."""
        u = self.update
        if not u or not u.get("installer") or u.get("status") in ("downloading", "installing"):
            return
        if self.games:
            self.log.warn("Close the game first: the update replaces the game files too")
            return
        u["status"] = "downloading"
        def run():
            try:
                path = os.path.join(tempfile.gettempdir(), "H2Link_Setup_%s.exe" % re.sub(r"[^\w.]", "", u["version"]))
                req = urllib.request.Request(u["installer"], headers={"User-Agent": "H2Link/" + VERSION})
                with urllib.request.urlopen(req, timeout=60) as r, open(path + ".part", "wb") as f:
                    shutil.copyfileobj(r, f)
                os.replace(path + ".part", path)
                u["status"] = "installing"
                self.log.info("Installing H2Link %s - H2Link closes now and starts again in a moment" % u["version"])
                # The installer must only start once this H2Link is completely gone: a silent installer that
                # finds H2Link.exe still in use gives up. So a hidden PowerShell waits for this process (and,
                # for H2Link.exe, the small launcher process that unpacked it) to end, then starts the
                # installer: no window and no questions (/VERYSILENT /SUPPRESSMSGBOXES). clean_env: see there.
                args = ["/VERYSILENT", "/SUPPRESSMSGBOXES", "/NORESTART", "/CLOSEAPPLICATIONS"]
                if IS_WIN:
                    pids = [os.getpid()] + ([os.getppid()] if getattr(sys, "frozen", False) else [])
                    ps = ("Wait-Process -Id %s -Timeout 60 -ErrorAction SilentlyContinue; "
                          "Start-Process -FilePath '%s' -ArgumentList %s"
                          % (",".join(str(x) for x in pids), path.replace("'", "''"),
                             ",".join("'%s'" % a for a in args)))
                    subprocess.Popen(["powershell", "-NoProfile", "-NonInteractive", "-WindowStyle", "Hidden",
                                      "-Command", ps], env=clean_env(), creationflags=0x08000000)
                else:
                    subprocess.Popen([path] + args, env=clean_env())
                # Then H2Link ends at once: the room hears it is leaving, and nothing else is worth waiting for.
                # The helper starts the installer the moment this process is gone.
                self.command("quit")
                close_page_window()
                time.sleep(0.3)
                self.log.flush(0.2)
                os._exit(0)
            except Exception as e:
                u["status"] = "failed"
                self.log.error("The update could not be downloaded (%s) - try again, or use the release page" % e)
        self.log.info("Downloading H2Link %s in the background..." % u["version"])
        threading.Thread(target=run, daemon=True).start()

    LOG_KEEP_DAYS = 7          # networking logs older than this go, except the newest few per slot
    LOG_KEEP_NEWEST = 5
    LOG_FULL_MAX = 20 << 20    # the cumulative debug_full log is cut back to its last LOG_FULL_KEEP beyond this
    LOG_FULL_KEEP = 8 << 20

    def clean_game_logs(self):
        """At start: the game writes a networking log for every run and keeps adding to debug_full_sNN.txt, so
        the H2EK's reports folder grows with every session. Networking logs older than a week go (the newest
        few of each slot always stay); an oversized debug_full log keeps its last 8 MB - the recent sessions,
        and with them any crash. Files a running game has open are left alone. Crashes are saved in a report
        when they happen (see _game_closed), so nothing here can lose one."""
        root = self.game_dir
        if not root or not os.path.isdir(root):
            return
        net, gone, freed = {}, 0, 0
        depth0 = root.rstrip("\\/").count(os.sep)
        for d, dirs, files in os.walk(root):
            if d.count(os.sep) - depth0 >= 2:
                dirs[:] = []
            for f in files:
                low, p = f.lower(), os.path.join(d, f)
                try:
                    if low.startswith("networking_debug_") and low.endswith(".txt"):
                        net.setdefault(low[-8:], []).append((os.path.getmtime(p), p))     # by "_sNN.txt"
                    elif low.startswith("debug_full") and low.endswith(".txt") and os.path.getsize(p) > self.LOG_FULL_MAX:
                        size = os.path.getsize(p)
                        with open(p, "rb") as fh:
                            fh.seek(size - self.LOG_FULL_KEEP)
                            fh.readline()                          # start on a whole line
                            tail = fh.read()
                        with open(p + ".h2link_new", "wb") as fh:
                            fh.write(tail)
                        try:
                            os.replace(p + ".h2link_new", p)       # fails while a game has it open: kept as is
                            gone, freed = gone + 1, freed + size - len(tail)
                        except OSError:
                            os.remove(p + ".h2link_new")
                except OSError:
                    pass
        cutoff = time.time() - self.LOG_KEEP_DAYS * 86400
        for logs in net.values():
            for mt, p in sorted(logs, reverse=True)[self.LOG_KEEP_NEWEST:]:
                if mt < cutoff:
                    try:
                        n = os.path.getsize(p)
                        os.remove(p)
                        gone, freed = gone + 1, freed + n
                    except OSError:
                        pass
        if gone:
            self.log.info("Tidied %d old game log file%s (%.1f MB freed)" % (gone, "" if gone == 1 else "s", freed / 1e6))

    CRASH_MARKS = (b"ASSERTION FAILED", b"### EXCEPTION", b"halt_and_catch_fire", b"crash_report")

    def _game_closed(self, slot):
        """A game window on this PC has closed. If its log ends in a crash, a report is saved right away -
        the game's logs as they are now, before anything can tidy them."""
        try:
            f = [x for x in self._game_logs(slot) if os.path.basename(x).lower().startswith("debug_full")]
            if not f:
                return
            with open(f[0], "rb") as fh:
                fh.seek(max(0, os.path.getsize(f[0]) - 16384))
                tail = fh.read()
            start = getattr(self, "_slot_start", {}).get(slot, 0)
            if os.path.getmtime(f[0]) < start or not any(m in tail for m in self.CRASH_MARKS):
                return
            self.log.warn("The game in slot %02d crashed - saving a report" % (slot + 1))
            self._cmd_report({"quiet": True})
            if self.report and os.path.isfile(self.report):
                self.cfg["crash_report"] = self.report           # offered on this page, and on the next start
                self.save_cfg()
        except OSError:
            pass

    def game_files_check(self):
        """At start (H2Link.exe): are the game files the ones this H2Link carries? Says so in the activity list
        when not - for example after an update whose game-file step could not run."""
        if not getattr(sys, "frozen", False) or not self.game_dir:
            return
        try:
            items, problems = _game_plan(self.game_dir, lambda *_: None)
        except Exception:
            return
        if problems:
            self.log.warn("The game files could not be updated: %s is not the H2EK's original. In Steam: Library > "
                          "H2EK > Properties > Installed Files > Verify integrity of tool files, then install H2Link "
                          "again." % ", ".join(os.path.basename(p.split(" - ")[0]) for p in problems))
        elif any(it["state"] != "up to date" for it in items):
            rc = install_game(self.game_dir, say=lambda *_: None)
            self.log.info("Game files updated for this H2Link" if rc == 0 else "The game files could not be updated")

    def _cmd_crash(self, d):
        """The crash notice: "view" shows the saved report in Explorer, "issues" opens the GitHub issues page
        in the browser, "dismiss" forgets it."""
        path = self.cfg.get("crash_report") or ""
        what = d.get("do")
        if what == "view" and path and os.path.isfile(path):
            if IS_WIN:
                subprocess.Popen(["explorer", "/select,", path], env=clean_env())
        elif what == "issues":
            webbrowser.open(ISSUES_URL)
        elif what == "dismiss":
            self.cfg.pop("crash_report", None)
            self.save_cfg()

    def _cmd_report(self, d):
        """One zip with everything needed to look into a problem."""
        try:
            folder = os.path.join(os.path.dirname(os.path.abspath(self.cfg_path)), "reports")
            os.makedirs(folder, exist_ok=True)
            who = re.sub(r"[^A-Za-z0-9_-]", "_", self.cfg.get("name", "player")) or "player"
            path = os.path.join(folder, "H2Link_%s_%s.zip" % (who, time.strftime("%Y%m%d_%H%M%S")))
            n = 0
            with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
                # H2Link's own part of a report carries no IP addresses: none are stored, any in text are masked.
                z.writestr("h2link_activity.txt", IP_RE.sub("x.x.x.x", self.log.text()))
                snap = dict(self.snap)
                for k in ("log", "my_pub", "lan", "share"):
                    snap.pop(k, None)
                snap["cfg"] = {k: v for k, v in snap.get("cfg", {}).items() if k not in ("password", "address", "server")}
                snap["peers_detail"] = [dict(name=p.name, slots=p.slots, rtt=p.rtt, relay_rtt=p.rtt_relay,
                                             path="none" if p.addr is None else "same network" if private_ip(p.addr[0])
                                             else "internet", candidates=len(p.cands),
                                             sent=p.tx_pk, received=p.rx_pk) for p in self.peers.values()]
                z.writestr("h2link_state.json", IP_RE.sub("x.x.x.x", json.dumps(snap, indent=1)))
                if self.game_dir:
                    for slot in (self.local_slots or [0]):
                        for f in self._game_logs(slot):
                            size = os.path.getsize(f)
                            with open(f, "rb") as fh:
                                if size > 6 << 20:          # the cumulative log can be huge; the end is what matters
                                    fh.seek(size - (6 << 20))
                                z.writestr("game/" + os.path.basename(f), fh.read())
                            n += 1
            self.report = path
            self.log.info("Report saved with %d game log file(s): %s" % (n, path))
            if n == 0:
                self.log.warn("No game logs found for slot %s in the game folder - the report only holds H2Link's side"
                              % slot_text(self.local_slots or [0]))
            if d.get("quiet"):
                self.log.info("Send this report along when you tell about the crash. It is in H2Link's reports folder.")
            elif IS_WIN:
                subprocess.Popen(["explorer", "/select,", path], env=clean_env())
        except Exception as e:
            self.log.error("Could not save the report (%s)" % e)

    # ---- room host: admission ------------------------------------------------
    def _alloc(self, want, pref, uuid):
        used = set(self.local_slots)
        for p in self.peers.values():
            if p.uuid != uuid:
                used |= set(p.slots)
        return alloc_slots(used, self.reserved, want, pref, uuid)

    def _reject(self, addr, nc, why):
        self._wan_send(HDR.pack(T_REJECT, 0xFF, 0xFF, MAGIC) + nc + why.encode(), addr)

    def _host_preauth(self, typ, body, addr, t):
        if typ == T_HELLO and len(body) >= 33:
            uuid, nc = body[1:17], body[17:33]
            if body[0] != PROTO:
                return self._reject(addr, nc, "This room runs a different %s version (%s)." % (APP, VERSION))
            pend = self.pending.get(addr)
            if not pend or pend[1] != nc:
                pend = self.pending[addr] = (uuid, nc, os.urandom(16), t)
            self._wan_send(HDR.pack(T_CHALLENGE, 0xFF, 0xFF, MAGIC) + nc + pend[2] + b"\x01", addr)
        elif typ == T_AUTH and len(body) > 64:
            uuid, ns, mac, js = body[:16], body[16:32], body[32:64], body[64:]
            pend = self.pending.get(addr)
            if not pend or pend[0] != uuid or pend[2] != ns:
                return
            nc = pend[1]
            if not hmac.compare_digest(mac, hmac.new(self.pwkey, b"auth" + nc + ns + uuid + js, "sha256").digest()):
                return self._reject(addr, nc, "Wrong room password.")
            try:
                info = json.loads(js.decode())
                want = min(MAX_WINDOWS, max(1, int(info.get("want", 1))))
                pref = [int(s) for s in info.get("pref", [])][:NSLOTS]
            except (ValueError, TypeError):
                return
            p = self.by_uuid.get(uuid)
            if p is not None and self.peers.get(p.id) is not p:
                p = None
            if (p is not None and addr != p.addr and now() - p.last_rx < 3.0
                    and int(info.get("epoch", 0) or 0) != p.epoch) or uuid == self.uuid:
                return self._reject(addr, nc, DUPLICATE)
            if p is None:
                nid = next((i for i in range(1, NSLOTS) if i not in self.peers), None)
                slots = self._alloc(want, pref, uuid) if nid is not None else None
                if slots is None:
                    return self._reject(addr, nc, "The room is full: all 16 slots are taken.")
                p = Peer(nid)
                p.uuid, p.slots, p.want = uuid, slots, want
                p.epoch = random.getrandbits(32) | 1
                self.admitted += 1
                p.since = self.admitted
                self.peers[nid] = self.by_uuid[uuid] = p
                self.log.info("%s joined and plays in slot %s"
                              % (str(info.get("name", "?"))[:24], slot_text(slots)))
            else:
                if want != p.want or set(pref) != set(p.slots):
                    slots = self._alloc(want, pref, uuid)
                    if slots is None:
                        return self._reject(addr, nc, "The room is full: all 16 slots are taken.")
                    p.slots, p.want = slots, want
                if int(info.get("epoch", 0)) != p.epoch:      # the other side restarted
                    p.epoch = random.getrandbits(32) | 1
                    self.admitted += 1
                    p.since = self.admitted
                    p.tx.reset()
                    p.rx.reset()
                    p.fresh = True
                    self.mirror.peer_gone(p.id)
            p.name = str(info.get("name", "?"))[:24]
            p.addr = p.pub = addr
            p.last_rx = t
            p.lport = int(info.get("lport", 0) or 0)
            p.lan = [(str(a[0]), int(a[1])) for a in info.get("lan", [])[:6] if len(a) == 2]
            out = json.dumps(dict(id=p.id, key=self.key.hex(), epoch=p.epoch, hepoch=self.epoch, slots=p.slots,
                                  room=self.room_name, you=list(addr), since=p.since)).encode()
            mac = hmac.new(self.pwkey, b"welc" + nc + ns + out, "sha256").digest()
            self._wan_send(HDR.pack(T_WELCOME, 0xFF, 0xFF, MAGIC) + nc + mac + out, addr)
            self._roster_changed()

    def _roster_changed(self):
        self._rebuild_owner()
        nodes = [dict(id=0, name=self.cfg["name"], epoch=self.epoch, slots=self.local_slots)]
        for p in self.peers.values():
            nodes.append(dict(id=p.id, name=p.name, epoch=p.epoch, slots=p.slots, pub=list(p.pub),
                              lan=[list(a) for a in p.lan], lport=p.lport, since=p.since))
        self.broadcast(bytes([M_ROSTER]) + json.dumps(dict(room=self.room_name, nodes=nodes)).encode())

    def _drop_peer(self, p, why):
        self.log.info("%s %s" % (p.name, why))
        if self.mirror:
            self.mirror.peer_gone(p.id)
        self.peers.pop(p.id, None)
        if self.is_host:
            self.by_uuid.pop(p.uuid, None)
            self._roster_changed()
        else:
            self._rebuild_owner()

    def _rebuild_owner(self):
        own = {}
        for p in self.peers.values():
            for s in p.slots:
                own[s] = p.id
        self.slot_owner = own
        me = self.my_id if self.my_id is not None else 0
        for p in self.peers.values():
            p.data_hdr = HDR.pack(T_DATA, me, p.id, self.key)

    # ---- joining a room --------------------------------------------------------
    def _hs_begin(self, t):
        self.hs_state, self.hs_start, self.hs_next = "hello", t, 0.0
        self.hs_nc = os.urandom(16)
        self.hs_auth = None

    def _hs_tick(self, t):
        if self.hs_state is None or t < self.hs_next:
            return
        self.hs_next = t + 0.5
        if self.hs_state == "hello":
            self._wan_send(HDR.pack(T_HELLO, 0xFF, 0xFF, MAGIC) + bytes([PROTO]) + self.uuid + self.hs_nc
                           + self.room_req.encode(), self.host_addr)
        elif self.hs_auth:
            self._wan_send(self.hs_auth, self.host_addr)
        if self.state == "connecting" and t - self.hs_start > 12:
            if self.server_room:
                self.error = ("No answer from the server%s. It may be down; try again in a moment."
                              % (" at " + self.host_text if self.host_text else ""))
            else:
                self.error = ("No answer from %s. Check the address, and that the host has UDP port %d forwarded "
                              "to the PC running %s." % (self.host_text, self.host_addr[1], APP))
            self.log.error(self.error)
            err = self.error
            self._leave()
            self.error = err

    def _client_preauth(self, typ, body, addr, t):
        if addr != self.host_addr or self.hs_state is None or body[:16] != self.hs_nc:
            return
        if typ == T_CHALLENGE and len(body) >= 32 and self.hs_state == "hello":
            ns = self.hs_ns = body[16:32]
            if self.in_room:
                pref = self.local_slots[:MAX_WINDOWS]
                want = len(pref)
            else:
                pref = self._running_slots()
                self._over_limit(pref)
                pref = pref[:MAX_WINDOWS]
                want = min(MAX_WINDOWS, max(self.cfg.get("want", 1), len(pref)))
            info = dict(name=self.cfg["name"], want=want, pref=pref, lport=self.wan_port, epoch=self.epoch,
                        lan=[[ip, self.wan_port] for ip in local_ips(self.host_addr[0])], v=VERSION, room=self.room_req)
            if self.server_room and len(body) > 32 and not body[32] & 1:
                info["create"] = self.pwkey.hex()
            js = json.dumps(info).encode()
            mac = hmac.new(self.pwkey, b"auth" + self.hs_nc + ns + self.uuid + js, "sha256").digest()
            self.hs_auth = HDR.pack(T_AUTH, 0xFF, 0xFF, MAGIC) + self.uuid + ns + mac + js
            self.hs_state, self.hs_next = "auth", 0.0
        elif typ == T_WELCOME and len(body) > 48 and self.hs_state == "auth":
            mac, js = body[16:48], body[48:]
            if not hmac.compare_digest(mac, hmac.new(self.pwkey, b"welc" + self.hs_nc + self.hs_ns + js, "sha256").digest()):
                return
            info = json.loads(js.decode())
            self.hs_state = None
            key = bytes.fromhex(info["key"])
            if not self.in_room or key != self.key or info["epoch"] != self.epoch:
                if self.mirror:
                    for nid in list(self.peers):
                        self.mirror.peer_gone(nid)
                self.peers = {}
            self.my_id, self.key, self.epoch = info["id"], key, info["epoch"]
            self.room_name = info.get("room", "")
            self.my_pub = info.get("you")
            self.server_room = bool(info.get("server"))
            self.relay_only = bool(info.get("relay"))
            self.since = int(info.get("since", 0))
            hp = self.peers.get(0)
            if hp is None or hp.epoch != info["hepoch"]:
                hp = self.peers[0] = Peer(0)
                hp.epoch, hp.name = info["hepoch"], "Server" if self.server_room else "Room host"
            hp.addr, hp.last_rx = self.host_addr, t
            if self.state != "connected":
                self.log.info("Joined %s" % (self.room_name or "the room"))
            if self.state == "connecting":
                self._net_start(self.host_addr[0])
            self.state = "connected"
            if sorted(info["slots"]) != self.local_slots or not self.mutexes:
                self._claim(info["slots"])
            self._rebuild_owner()
        elif typ == T_REJECT:
            why = body[16:].decode("utf-8", "replace") or "The room host refused the connection."
            self.log.error(why)
            self._leave()
            self.error = why

    def _on_roster(self, info, t):
        self.room_name = info.get("room", self.room_name)
        seen = set()
        for n in info.get("nodes", []):
            nid = int(n["id"])
            if nid == self.my_id:
                self.my_pub = n.get("pub", self.my_pub)
                self.since = int(n.get("since", self.since))
                continue
            seen.add(nid)
            p = self.peers.get(nid)
            if p is None:
                p = self.peers[nid] = Peer(nid)
                p.epoch = n["epoch"]
            elif p.epoch != n["epoch"]:
                self.mirror.peer_gone(nid)
                p.epoch = n["epoch"]
                p.tx.reset()
                p.rx.reset()
                p.fresh = True
            if p.name != n["name"] and nid != 0 and p.name == "?":
                self.log.info("%s is in the room, slot %s" % (n["name"], slot_text(n["slots"])))
            p.name, p.slots = str(n["name"])[:24], [int(s) for s in n["slots"]]
            p.since = int(n.get("since", 0))
            if nid != 0:
                cands = []
                pub = n.get("pub")
                if pub:
                    cands.append((pub[0], int(pub[1])))
                    if n.get("lport"):
                        cands.append((pub[0], int(n["lport"])))
                for a in n.get("lan", []):
                    cands.append((a[0], int(a[1])))
                p.cands = list(dict.fromkeys(cands))[:8]
        for nid in [k for k in self.peers if k not in seen]:
            self._drop_peer(self.peers[nid], "left the room")
        self._rebuild_owner()

    # ---- packets from the internet ---------------------------------------------
    def _drain_wan(self, t):
        sock = self.sock
        for _ in range(128):
            try:
                data, addr = sock.recvfrom(65535)
            except (BlockingIOError, InterruptedError):
                return
            except OSError:
                continue
            if len(data) >= 7:
                self._on_wan(data, addr, t)
                if self.sock is not sock:
                    return

    def _on_wan(self, data, addr, t):
        if data[4:8] == STUN_COOKIE:
            got = stun_parse(data, self.stun_txid) if self.stun_txid else None
            if got and not self.pub_ip:
                self.pub_ip = got[0]
                if self.is_host:
                    self.log.info("Room address for other players: %s:%d" % (self.pub_ip, self.wan_port))
                self._check_reach()
            return
        typ, src, dst = data[0], data[1], data[2]
        if typ < T_PING:
            if data[3:7] == MAGIC:
                if self.is_host:
                    self._host_preauth(typ, data[7:], addr, t)
                elif self.mode == "client":
                    self._client_preauth(typ, data[7:], addr, t)
            return
        if not self.key or data[3:7] != self.key:
            return
        p = self.peers.get(src)
        if dst != self.my_id:
            if self.is_host and p is not None and addr == p.addr:   # relay between two players
                q = self.peers.get(dst)
                p.last_rx = t
                if q is not None and q.addr:
                    self._wan_send(data, q.addr)
            return
        if p is None:
            return
        if self.is_host:
            if addr != p.addr:
                return
            direct = True
        elif src == 0:
            if addr != self.host_addr:
                return
            direct = True
        else:
            direct = addr != self.host_addr
            if direct and self.opts.no_direct:
                return
        if direct and addr == p.addr:
            p.last_rx = t
        if typ == T_DATA:
            if len(data) > 10:
                sslot, dslot, pidx = data[7], data[8], data[9]
                s = self.slot_socks.get((sslot, pidx))
                if s is not None and dslot in self.local_set and self.slot_owner.get(sslot) == src:
                    p.rx_pk += 1
                    p.rx_by += len(data) - 10
                    try:
                        # From the sender's slot port: the game identifies a sender by source port.
                        s.sendto(data[10:], (self.loop_ip, BASE_PORTS[pidx] + dslot * SPACING))
                    except OSError:
                        pass
        elif typ == T_REL:
            if len(data) > REL_HDR.size:
                _, _, _, _, se, de, seq, flags = REL_HDR.unpack_from(data)
                if de == self.epoch and se == p.epoch:
                    for msg in p.rx.on_pkt(seq, flags, data[REL_HDR.size:]):
                        self._on_msg(p, msg, t)
        elif typ == T_RACK:
            if len(data) >= RACK_HDR.size:
                _, _, _, _, ae, se, cum, bm = RACK_HDR.unpack_from(data)
                if se == self.epoch and ae == p.epoch:
                    p.tx.on_ack(t, cum, bm, lambda pkt: self._send_peer(p, pkt, t))
                    self._pump(p, t)
        elif typ == T_PING or typ == T_PONG:
            if len(data) < PING_HDR.size:
                return
            token, games = PING_HDR.unpack_from(data)[4:6]
            p.games = games
            if typ == T_PING:
                pong = PING_HDR.pack(T_PONG, self.my_id, src, self.key, token, self.games)
                if direct:
                    self._wan_send(pong, addr)
                else:
                    self._send_peer(p, pong, t)
            else:
                sent = p.tokens.pop(token, None)
                if sent is None:
                    return
                r = t - sent
                if direct:
                    if p.addr != addr or t - p.last_rx > DIRECT_TIMEOUT:
                        if src != 0 and not self.is_host:
                            self.log.info("Direct link to %s%s" % (p.name, " (same network)" if private_ip(addr[0]) else ""))
                        p.addr = addr
                    p.last_rx = t
                    p.rtt = r if p.rtt is None else 0.8 * p.rtt + 0.2 * r
                else:
                    p.rtt_relay = r if p.rtt_relay is None else 0.8 * p.rtt_relay + 0.2 * r
        elif typ == T_BYE:
            if self.is_host:
                self._drop_peer(p, "left the room")
            elif src == 0:
                self.log.warn("The room host closed the room")
                self._leave()
                self.error = "The host closed the room."

    def _on_msg(self, p, msg, t):
        kind = msg[0]
        if kind == M_ROSTER:
            if p.id == 0 and not self.is_host:
                try:
                    self._on_roster(json.loads(msg[1:].decode()), t)
                except (ValueError, KeyError, TypeError):
                    pass
        elif kind == M_GO:
            rh = self.room_host()
            if rh is not None and rh.id == p.id and not self.i_host_room():
                if not self.cfg.get("auto_start", True):
                    self.log.info("%s launched the game - press Start the game to join" % p.name)
                elif self.games or self.launch_wait:
                    pass                                    # a game is running or about to start already
                else:
                    n = len(self.local_slots)
                    self.log.info("%s launched the game - starting yours (%d window%s): %s joins %s's lobby, and the "
                                  "level starts when everyone is in" % (p.name, n, "" if n == 1 else "s",
                                                                       "it" if n == 1 else "each", p.name))
                    self._cmd_launch({"now": True, "go": True})  # straight to the host's lobby, not after its level
                    # Each window reads init.txt as it starts, so the next one is started only after a pause.
                    self.go_more, self.go_next = n - 1, now() + GO_SPACING
                self.host_lobby = True
        elif kind == M_CHAT:
            try:
                text = " ".join(str(json.loads(msg[1:].decode())["text"]).split())[:300]
            except (ValueError, KeyError, TypeError):
                return
            if text and self.is_player(p):
                self._chat_add(p.name, text, False)
        elif kind == M_CHATLOG:
            if p is self.room_host() and not self.chat:
                try:
                    for e in json.loads(msg[1:].decode())[-50:]:
                        text = " ".join(str(e["t"]).split())[:300]
                        if text:
                            self.chat_seq += 1
                            self.chat.append((self.chat_seq, float(e.get("w", 0)) or time.time(),
                                              str(e["n"])[:24], text, False))
                except (ValueError, KeyError, TypeError):
                    pass
        elif kind == M_ROLE and len(msg) >= 2:
            p.hosting = bool(msg[1])
        elif kind == M_AUTO and len(msg) >= 2:
            p.auto_start = bool(msg[1])
        elif kind == M_LIVE and len(msg) >= 2:
            if p is self.room_host():
                self.host_live, self.live_from = (None if msg[1] == 2 else bool(msg[1])), p.id
        elif kind == M_ROOM:
            if p is self.room_host():           # only the room host decides
                try:
                    plan = clean_plan(json.loads(msg[1:].decode()))
                except (ValueError, TypeError, AttributeError):
                    plan = None
                if plan:
                    if plan != self.plan or not self.plan_known:
                        self.log.info("%s set the room to %s" % (p.name, plan_text(plan)))
                    self.plan, self.plan_known = plan, True
        elif self.mirror:
            self.mirror.on_msg(p, kind, msg[1:], t)

    def _pump(self, p, t):
        if p.tx.queue:
            me, key, ep = self.my_id, self.key, self.epoch
            p.tx.pump(t, lambda seq, flags, chunk: REL_HDR.pack(T_REL, me, p.id, key, ep, p.epoch, seq, flags) + chunk,
                      lambda pkt: self._send_peer(p, pkt, t))

    # ---- packets from the local game ---------------------------------------------
    def _drain_slot(self, sock, rslot, pidx, t):
        base = BASE_PORTS[pidx]
        local = self.local_set
        for _ in range(64):
            try:
                data, addr = sock.recvfrom(4096)
            except (BlockingIOError, InterruptedError):
                return
            except OSError:
                continue
            lslot, rem = divmod(addr[1] - base, SPACING)
            if rem or lslot not in local:
                self.stray += 1
                continue
            nid = self.slot_owner.get(rslot)
            p = self.peers.get(nid) if nid is not None else None
            if p is None:
                continue                # nobody plays in that slot
            a = self.route(p, t)
            if a:
                self._wan_send(p.data_hdr + bytes((lslot, rslot, pidx)) + data, a)
                p.tx_pk += 1
                p.tx_by += len(data)

    # ---- timers ------------------------------------------------------------------
    def guest_name(self, name):
        """True for names the game signs in with that are not a saved profile the player chose: the game's
        Guest, H2Link 1.0.9's "Guest (n)", and the room names H2Link gives guest windows (1.0.10+)."""
        n = name.strip().lower()
        if re.fullmatch(r"guest( \(\d+\))?", n):
            return True
        bases = [self.cfg.get("name", "")] + [p.name for p in self.peers.values()]
        return any(n == window_name(b, k).lower() for b in bases if b for k in range(NSLOTS + 1))

    def last_profile(self, t):
        """The saved profile last signed in with in the game on this PC, from the newest networking logs,
        passing over guest sign-ins (the room-name guests of further windows, Guest)."""
        if t < self._prof_next:
            return self._prof
        self._prof_next = t + 20.0
        root, logs = self.game_dir, []
        if root and os.path.isdir(root):
            try:
                depth0 = root.rstrip("\\/").count(os.sep)
                for d, dirs, files in os.walk(root):
                    if d.count(os.sep) - depth0 >= 2:
                        dirs[:] = []
                    for f in files:
                        if f.lower().startswith("networking_debug_") and f.lower().endswith(".txt"):
                            p = os.path.join(d, f)
                            logs.append((os.path.getmtime(p), p))
                for _, path in sorted(logs, reverse=True)[:40]:          # newest first
                    with open(path, "rb") as f:
                        hits = re.findall(rb"lifecycle: UI-CONTROLLER-SIGNIN 0 ([^\r\n]{1,16})", f.read(1 << 20))
                    names = [h.decode("latin1").strip() for h in hits]
                    names = [n for n in names if n and not self.guest_name(n)]
                    if names:
                        self._prof = names[-1]
                        break
            except OSError:
                pass
        return self._prof

    def _level_poll(self, t):
        """Room host: follow the game's own networking log to know when the level has finished loading."""
        slot = next((s for s in self.local_slots if self.games >> s & 1), None)
        if slot is None:
            self.level_tail, self.level_since = None, None
            return False
        if self.level_since is None:
            self.level_since = t
        tail = self.level_tail
        if tail is None or t >= self.level_scan:
            self.level_scan = t + 3.0
            try:
                logs = [f for f in self._game_logs(slot) if os.path.basename(f).lower().startswith("networking_debug_")]
            except OSError:
                logs = []
            logs = [f for f in logs if os.path.getmtime(f) >= time.time() - (t - self.level_since) - 30]
            if logs and (tail is None or tail[0] != logs[0]):
                tail = self.level_tail = [logs[0], 0, False, t, False]
        if tail is None:
            # no log to read (unusual folder layout): after a while say "cannot tell", so nobody waits for ever
            return None if t - self.level_since > 15.0 else False
        try:
            with open(tail[0], "rb") as f:
                f.seek(tail[1])
                chunk = f.read(1 << 20)
        except OSError:
            return False
        cut = chunk.rfind(b"\n")
        if cut >= 0:
            tail[1] += cut + 1
            for line in chunk[:cut].split(b"\n"):
                # The host's log, in order: "main_game_unload()", "lifecycle: MAP-LOADED <level>",
                # "MAP-LOAD (<level>) succeeded", "update_authority_join: JOIN-COMPLETE ...".
                if b"lifecycle: MAP-LOADED " in line:
                    tail[2], tail[3], tail[4] = b"\\ui\\mainmenu" not in line.lower(), t, False
                elif b"JOIN-COMPLETE" in line:
                    if tail[2] and not tail[4]:
                        tail[3], tail[4] = t, True          # the host's game has left its start-up wait
                elif b"main_game_unload" in line or (b"MAP-LOAD (" in line and b"pending" in line):
                    tail[2] = tail[4] = False
        # live a little after the game says its start is complete; if that line never comes, after its
        # start-up wait must be over anyway
        return tail[2] and t - tail[3] >= (3.0 if tail[4] else 35.0)

    def _slow(self, t):
        if t >= self._upd_next and not self._upd_busy:
            self._upd_next = t + UPDATE_EVERY
            self._upd_busy = True
            threading.Thread(target=self._check_update, daemon=True).start()
        if self.mode == "client":
            self._hs_tick(t)
        if not self.in_room:
            return
        h = self.hosting()
        if h != self.hosting_sent:
            self.hosting_sent = h
            self.broadcast(bytes([M_ROLE, 1 if h else 0]))
        if self.cfg.get("launched_as") and not self.games and t - self.launch_t > 30.0:
            self.cfg["launched_as"] = ""            # that game is gone
            self.save_cfg()
        if self.i_host_room():
            up = self._level_poll(t)
            if not self.was_host:
                self.send_plan()                            # taking over as room host: this PC's settings count now
            if up != self.level_up or not self.was_host:    # also once on taking over as room host
                self.level_up = up
                self.broadcast(bytes([M_LIVE, 2 if up is None else 1 if up else 0]))
            self.host_live, self.was_host = up, True
        else:
            self.was_host = False
            rh = self.room_host()
            if self.host_live is not None and (rh is None or rh.id != self.live_from):
                self.host_live = None                       # the room has a new host: wait for its word
        self.snapper.poll(t)
        if self.go_more and t >= self.go_poll:
            self.go_poll = t + 0.5
            if self._window_read_init(self._launch_slot, getattr(self, "launch_wall", 0.0)):
                self.go_next = min(self.go_next, t + 0.5)  # it has its settings: the next one can go
        if self.go_more and t >= self.go_next:
            self.go_more -= 1
            self.go_next = t + GO_SPACING
            if any(not self.plat.mutex_exists(s) for s in self.local_slots):
                self._cmd_launch({"now": True, "go": True})
            else:
                self.go_more = 0
        if self.host_live:
            self.host_lobby = False                         # the host's level is up: later games join in progress
        if self.launch_wait and self.host_live is not False:
            self.launch_wait = False
            self.log.info("The host's level is loaded - starting the game" if self.host_live
                          else "The host cannot tell when its level is loaded - starting the game")
            self._cmd_launch({"now": True})
        if self.stun_addrs and not self.pub_ip and self.stun_tries < 6 and t >= self.stun_next:
            self.stun_tries += 1
            self.stun_next = t + 1.5
            for a in self.stun_addrs:
                self._wan_send(b"\x00\x01\x00\x00" + STUN_COOKIE + self.stun_txid, a)
        g = 0
        for s in self.local_slots:
            if self.plat.mutex_exists(s):
                g |= 1 << s
        if g != self.games:
            if not hasattr(self, "_slot_start"):
                self._slot_start = {}
            for s in range(NSLOTS):
                if g >> s & 1 and not self.games >> s & 1:
                    self._slot_start[s] = time.time()
                elif self.games >> s & 1 and not g >> s & 1:
                    threading.Thread(target=self._game_closed, args=(s,), daemon=True).start()
        self.games = g
        self._tidy_poll(t)
        for p in list(self.peers.values()):
            if self.is_host and t - p.last_rx > NODE_SILENT:
                self._drop_peer(p, "stopped answering and was removed")
                continue
            if t < p.next_ping:
                continue
            token = random.getrandbits(32)
            p.tokens[token] = t
            while len(p.tokens) > 24:
                p.tokens.popitem(last=False)
            pkt = PING_HDR.pack(T_PING, self.my_id, p.id, self.key, token, self.games)
            p.next_ping = t + 1.0
            if self.is_host or p.id == 0:
                if p.addr:
                    self._wan_send(pkt, p.addr)
                continue
            if p.addr is not None and t - p.last_rx < DIRECT_TIMEOUT:
                self._wan_send(pkt, p.addr)
                continue
            if p.addr is not None:
                self.log.warn("Direct link to %s lost - relaying through the %s"
                              % (p.name, "server" if self.server_room else "room host"))
                p.addr, p.rtt = None, None
            if not self.opts.no_direct:
                for c in p.cands:
                    self._wan_send(pkt, c)
            token = random.getrandbits(32)
            p.tokens[token] = t
            self._wan_send(PING_HDR.pack(T_PING, self.my_id, p.id, self.key, token, self.games), self.host_addr)
            if t - p.born > 30:
                p.next_ping = t + 3.0
        if self.is_host:
            for a in [a for a, v in self.pending.items() if t - v[3] > 30]:
                del self.pending[a]
        else:
            hp = self.peers.get(0)
            if hp and t - hp.last_rx > HOST_SILENT and self.hs_state is None:
                if self.state == "connected":
                    self.log.warn("The %s stopped answering - trying to reconnect"
                                  % ("server" if self.server_room else "room host"))
                self.state = "reconnecting"
                self._hs_begin(t)
            elif hp and self.state == "reconnecting" and self.hs_state is None:
                self.state = "connected"

    def _snapshot(self):
        t = now()
        slots = [dict(slot=s, state="open") for s in range(NSLOTS)]
        peers = []
        if self.in_room:
            groups = []                 # one per PC: (room host first?, lowest slot, rows)
            sn = self.slot_names()
            mine = [dict(slot=s, state="you", name=sn.get(s, self.cfg["name"]), game=bool(self.games >> s & 1),
                         host=self.i_host_room()) for s in sorted(self.local_slots) if 0 <= s < NSLOTS]
            if mine:
                groups.append(mine)
            for p in self.peers.values():
                if self.is_host or p.id == 0:
                    link = "direct" if t - p.last_rx < DIRECT_TIMEOUT else "silent"
                    rtt = p.rtt
                elif p.addr is not None and t - p.last_rx < DIRECT_TIMEOUT:
                    link, rtt = "direct", p.rtt
                else:
                    link, rtt = "relayed", p.rtt_relay
                ms = None if rtt is None else int(rtt * 1000 + 0.5)
                rows = [dict(slot=s, state="player", name=sn.get(s, p.name), link=link, ms=ms,
                             game=bool(p.games >> s & 1), host=p is self.room_host())
                        for s in sorted(p.slots) if 0 <= s < NSLOTS]
                if rows:
                    groups.append(rows)
                peers.append(dict(id=p.id, name=p.name, slots=p.slots, link=link, ms=ms, tx=p.tx_pk, rx=p.rx_pk,
                                  player=self.is_player(p),
                                  queued=len(p.tx.queue) + len(p.tx.inflight)))
            # The list on the page: the room host's PC on top, then the other PCs by their first slot, each
            # PC's windows together, and the open slots after everyone. A PC's second and later windows are
            # shown as "Name (1)", "Name (2)"... (slot_names, also the names the games sign in with). Each row
            # keeps its real game slot in "slot".
            groups.sort(key=lambda g: (not g[0]["host"], g[0]["slot"]))
            rows = []
            for g in groups:
                rows += g
            used = {r["slot"] for r in rows}
            slots = (rows + [c for c in slots if c["slot"] not in used])[:NSLOTS]
        warns = []
        busy = sorted({"%02d" % (c[0] + 1) for c in self.conflicts if not c[2]})
        if busy:
            warns.append("Slot %s is occupied on this PC by something else. Close every game window and start "
                         "the game again from here." % ", ".join(busy))
        denied = sorted({str(c[1]) for c in self.conflicts if c[2]})
        if denied:
            warns.append("Windows has reserved UDP port %s, so the player in that slot cannot be reached "
                         "from this PC." % ", ".join(denied))
        if self.in_room and not self.game_dir:
            warns.append("No game folder set. Without it a join in progress cannot deliver the save to this PC.")
        if self.state == "reconnecting":
            warns.append("The %s is not answering. Reconnecting. Players already linked directly keep playing."
                         % ("server" if self.server_room else "room host"))
        share = None
        run_exe = self._find_exe(self.plan["tick"]) or self._find_exe()
        ext = self.upnp.get("ext_ip") if self.upnp else None
        if self.is_host:
            ip = self.pub_ip or (ext if ext and not private_ip(ext) else None)
            share = (ip if self.wan_port == DEFAULT_PORT else "%s:%d" % (ip, self.wan_port)) if ip else None
        router = None if self.upnp is None else ("open" if self.upnp["ok"] else "closed")
        c = self.cfg
        self.snap = dict(
            share=share, router=router, report=self.report, on_server=self.server_room, relay_only=self.relay_only,
            i_host=self.i_host_room(), host_name=self.room_host().name if self.room_host() else c.get("name", ""),
            launch_wait=self.launch_wait, host_live=self.host_live,
            host_started=bool(self.host_lobby or self.host_live),
            update=self.update,
            crash=(self.cfg.get("crash_report") if self.cfg.get("crash_report") and
                   os.path.isfile(self.cfg["crash_report"]) else None),
            plan=dict(self.plan, known=self.plan_known or self.i_host_room(), text=plan_text(self.plan)),
            chat=[list(c) for c in self.chat],
            levels=[list(x) for x in LEVELS], difficulties=list(DIFFICULTIES), ticks=[list(x) for x in TICKS],
            skulls=[[g, [list(i) for i in items]] for g, items in SKULLS],
            exe_ver=self._exe_info(run_exe)[0] if run_exe else 0, auto_exe=AUTO_EXE,
            have_tick=[t for t, _ in TICKS if self._find_exe(t)],
            players=(len(self.local_slots) + sum(len(p.slots) for p in self.peers.values() if self.is_player(p)))
                    if self.in_room else 0,                    # game windows (players), not PCs
            app=APP, version=VERSION, mode=self.mode, state=self.state, error=self.error, room=self.room_name,
            host=self.host_text, port=getattr(self, "wan_port", c["port"]), my_slots=self.local_slots,
            my_pub=self.my_pub, lan=self.lan_ips if self.is_host else [], slots=slots, peers=peers, warnings=warns,
            games=[s for s in self.local_slots if self.games >> s & 1], stray=self.stray,
            sync=self.mirror.last_sync if self.mirror else None, exe=os.path.basename(run_exe or ""),
            cfg=dict(name=c.get("name", ""), game_dir=c.get("game_dir", ""), exe=c.get("exe", ""),
                     args=c.get("args", ""), port=c.get("port", DEFAULT_PORT), want=c.get("want", 1),
                     password=c.get("password", ""), address=c.get("address", ""), room=c.get("room", ""),
                     server="" if read_server_key(c.get("server", "")) else c.get("server", ""),
                     builtin=bool(read_server_key(c.get("server", ""))), skip_picker=bool(c.get("skip_picker")),
                     auto_start=bool(c.get("auto_start", True)), snap_windows=bool(c.get("snap_windows", True)),
                     profile=c.get("profile", "")),
            seen_profile=self.last_profile(now()),
            log=self.log.tail())

    # ---- main loop ---------------------------------------------------------------
    def run(self):
        while not self.stop_flag:
            try:
                self._loop_once()
            except Exception as e:          # keep the tunnel alive, but say what happened
                import traceback
                self.log.error("Internal error: %s" % e)
                traceback.print_exc()
                time.sleep(0.2)
        self._leave()

    def _loop_once(self):
        if self.sel.get_map():
            events = self.sel.select(0.004)
        else:
            events = ()
            time.sleep(0.02)
        t = now()
        for key, _ in events:
            if key.data is None:
                self._drain_wan(t)
            else:
                self._drain_slot(key.fileobj, key.data[0], key.data[1], t)
            if self.sock is None:
                break                       # the room was left while handling a packet
        while not self.cmds.empty():
            cmd = self.cmds.get()
            fn = getattr(self, "_cmd_" + cmd[0], None)
            if cmd[0] == "leave":
                self._leave()
            elif cmd[0] == "settings":
                self._apply_settings(cmd[1])
            elif cmd[0] == "quit":
                self.stop_flag = True
            elif fn:
                fn(cmd[1] if len(cmd) > 1 else {})
            self.next_snap = 0.0
        while not self.inbox.empty():
            item = self.inbox.get()
            if item[0] in ("stun_addrs", "upnp"):
                self._on_net(item, t)
                continue
            m = self.mirror
            if m is None:
                continue
            if item[0] == "js_ready":
                m.on_ready(*item[1:], t)
            elif item[0] == "js_read_fail":
                m.on_read_fail(*item[1:])
            elif item[0] == "js_written":
                m.on_written(*item[1:], t)
            elif item[0] == "js_write_fail":
                m.on_write_fail(*item[1:])
        if self.delayed:
            keep = []
            for item in self.delayed:
                if item[0] <= t and self.sock:
                    try:
                        self.sock.sendto(item[1], item[2])
                    except OSError:
                        pass
                elif item[0] > t:
                    keep.append(item)
            self.delayed = keep
        if self.in_room and self.mirror:
            self.mirror.poll(t)
            for p in self.peers.values():
                if p.fresh:
                    p.fresh = False
                    self.mirror.snapshot_for(p)
                if p.rx.ack_due:
                    cum, bm = p.rx.ack()
                    self._send_peer(p, RACK_HDR.pack(T_RACK, self.my_id, p.id, self.key, self.epoch, p.epoch, cum, bm), t)
                if p.tx.queue:
                    self._pump(p, t)
            if t >= self.next_fast:
                self.next_fast = t + 0.02
                for p in self.peers.values():
                    if p.tx.inflight:
                        p.tx.tick(t, lambda pkt, p=p: self._send_peer(p, pkt, t))
        if t >= self.next_slow:
            self.next_slow = t + 0.25
            self._slow(t)
        if t >= self.next_snap:
            self.next_snap = t + 0.5
            self._snapshot()


# ===========================================================================
# Lobby server: runs on a machine that is always on. It keeps the rooms, gives
# every PC its slot, introduces the PCs to each other so they can link directly,
# and relays for pairs that cannot. It runs no game and needs none.
# ===========================================================================
class Room:
    def __init__(self, name, pwkey):
        self.name, self.pwkey = name, pwkey
        self.key = os.urandom(4)
        self.epoch = random.getrandbits(32) | 1
        self.peers = {}
        self.by_uuid = {}
        self.reserved = {}
        self.admitted = 0
        self.empty_since = now()
        self.locked = pwkey != room_key_of("")


class Server:
    MAX_ROOMS = 200
    EMPTY_KEEP = 120.0                 # an empty room keeps its slots this long for PCs that come back

    def __init__(self, bind, port, log, relay_only=False):
        self.log = log
        self.relay_only = relay_only    # hand out no addresses: PCs never learn where the others are
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind((bind or "0.0.0.0", port))
        self.sock.setblocking(False)
        for opt in (socket.SO_RCVBUF, socket.SO_SNDBUF):
            try:
                self.sock.setsockopt(socket.SOL_SOCKET, opt, 4 << 20)
            except OSError:
                pass
        Platform.no_connreset(None, self.sock)
        self.rooms = {}                 # lower-case name -> Room
        self.by_key = {}                # room key -> Room
        self.pending = {}               # address -> (uuid, client nonce, server nonce, time, room name)
        self.work = set()               # (room, peer) with an ack to send or data to pump
        self.flying = set()             # (room, peer) with unacknowledged data
        self.stop = False
        self.relayed = 0

    def send(self, pkt, addr):
        try:
            self.sock.sendto(pkt, addr)
            return True
        except (BlockingIOError, InterruptedError):
            return False
        except OSError:
            return True

    def reject(self, addr, nc, why):
        self.send(HDR.pack(T_REJECT, 0xFF, 0xFF, MAGIC) + nc + why.encode(), addr)

    def run(self):
        next_fast = next_slow = 0.0
        while not self.stop:
            try:
                ready, _, _ = select.select([self.sock], [], [], 0.01)
            except (OSError, ValueError):
                break
            t = now()
            if ready:
                for _ in range(512):
                    try:
                        data, addr = self.sock.recvfrom(65535)
                    except (BlockingIOError, InterruptedError):
                        break
                    except OSError:
                        continue
                    if len(data) >= 7:
                        try:
                            self.on_packet(data, addr, t)
                        except Exception as e:      # one bad packet must not stop the server
                            self.log.error("Packet from %s:%d dropped: %r" % (addr[0], addr[1], e))
            if self.work:
                work, self.work = self.work, set()
                for room, p in work:
                    if room.peers.get(p.id) is not p:
                        continue
                    if p.rx.ack_due:
                        cum, bm = p.rx.ack()
                        self.send(RACK_HDR.pack(T_RACK, 0, p.id, room.key, room.epoch, p.epoch, cum, bm), p.addr)
                    if p.tx.queue:
                        p.tx.pump(t, lambda seq, flags, chunk, room=room, p=p: REL_HDR.pack(
                            T_REL, 0, p.id, room.key, room.epoch, p.epoch, seq, flags) + chunk,
                            lambda pkt, p=p: self.send(pkt, p.addr))
                    if p.tx.inflight:
                        self.flying.add((room, p))
            if t >= next_fast:
                next_fast = t + 0.02
                for item in list(self.flying):
                    room, p = item
                    if room.peers.get(p.id) is not p or not p.tx.inflight:
                        self.flying.discard(item)
                        if p.tx.queue:
                            self.work.add(item)
                    else:
                        p.tx.tick(t, lambda pkt, p=p: self.send(pkt, p.addr))
            if t >= next_slow:
                next_slow = t + 1.0
                self.slow(t)
        self.sock.close()

    def slow(self, t):
        for room in list(self.rooms.values()):
            for p in list(room.peers.values()):
                if t - p.last_rx > NODE_SILENT:
                    self.drop(room, p, "stopped answering")
            if room.peers:
                room.empty_since = t
            elif t - room.empty_since > self.EMPTY_KEEP:
                del self.rooms[room.name.lower()]
                del self.by_key[room.key]
                self.log.info("Room \"%s\" closed (empty)" % room.name)
        for a in [a for a, v in self.pending.items() if t - v[3] > 30]:
            del self.pending[a]

    def drop(self, room, p, why):
        self.log.info("[%s] %s %s" % (room.name, p.name, why))
        room.peers.pop(p.id, None)
        room.by_uuid.pop(p.uuid, None)
        self.roster(room)

    def roster(self, room):
        nodes = [dict(id=0, name="Server", epoch=room.epoch, slots=[], since=0)]
        for p in room.peers.values():
            n = dict(id=p.id, name=p.name, epoch=p.epoch, slots=p.slots, since=p.since)
            if not self.relay_only:
                n.update(pub=list(p.pub), lan=[list(a) for a in p.lan], lport=p.lport)
            nodes.append(n)
        msg = bytes([M_ROSTER]) + json.dumps(dict(room=room.name, nodes=nodes)).encode()
        for p in room.peers.values():
            p.tx.enqueue(msg)
            self.work.add((room, p))

    def on_packet(self, data, addr, t):
        typ, src, dst = data[0], data[1], data[2]
        if typ < T_PING:
            if data[3:7] == MAGIC:
                self.preauth(typ, data[7:], data, addr, t)
            return
        room = self.by_key.get(data[3:7])
        p = room.peers.get(src) if room else None
        if p is None or p.addr != addr:
            return
        p.last_rx = now()
        if dst != 0:                    # relay between two PCs that have no direct link
            q = room.peers.get(dst)
            if q is not None:
                self.send(data, q.addr)
                self.relayed += 1
        elif typ == T_PING:
            if len(data) >= PING_HDR.size:
                token, games = PING_HDR.unpack_from(data)[4:6]
                self.send(PING_HDR.pack(T_PONG, 0, src, room.key, token, 0), addr)
        elif typ == T_REL:
            if len(data) > REL_HDR.size:
                _, _, _, _, se, de, seq, flags = REL_HDR.unpack_from(data)
                if de == room.epoch and se == p.epoch:
                    p.rx.on_pkt(seq, flags, b"")          # nothing a PC sends is meant for the server; just acknowledge
                    self.work.add((room, p))
        elif typ == T_RACK:
            if len(data) >= RACK_HDR.size:
                _, _, _, _, ae, se, cum, bm = RACK_HDR.unpack_from(data)
                if se == room.epoch and ae == p.epoch:
                    p.tx.on_ack(t, cum, bm, lambda pkt: self.send(pkt, p.addr))
                    self.work.add((room, p))
        elif typ == T_BYE:
            self.drop(room, p, "left")

    def preauth(self, typ, body, raw, addr, t):
        if typ == T_LIST and len(body) >= 8:
            rooms = sorted(({"name": r.name, "players": sum(max(1, len(getattr(p, "slots", []) or [])) for p in r.peers.values()),
                             "locked": r.locked}
                            for r in self.rooms.values() if r.peers), key=lambda r: -r["players"])
            while True:                 # never answer with more bytes than were asked with
                out = HDR.pack(T_ROOMS, 0xFF, 0xFF, MAGIC) + body[:8] + json.dumps(rooms).encode()
                if len(out) <= len(raw) or not rooms:
                    break
                rooms.pop()
            if len(out) <= len(raw):
                self.send(out, addr)
        elif typ == T_HELLO and len(body) >= 33:
            uuid, nc = body[1:17], body[17:33]
            if body[0] != PROTO:
                return self.reject(addr, nc, "This server runs %s %s. Get the same version." % (APP, VERSION))
            name = clean_room(body[33:97].decode("utf-8", "replace"))
            if not name:
                return self.reject(addr, nc, "Type a room name.")
            pend = self.pending.get(addr)
            if not pend or pend[1] != nc:
                if len(self.pending) > 5000:
                    return
                pend = self.pending[addr] = (uuid, nc, os.urandom(16), t, name)
            exists = name.lower() in self.rooms
            self.send(HDR.pack(T_CHALLENGE, 0xFF, 0xFF, MAGIC) + nc + pend[2] + bytes([1 if exists else 0]), addr)
        elif typ == T_AUTH and len(body) > 64:
            uuid, ns, mac, js = body[:16], body[16:32], body[32:64], body[64:]
            pend = self.pending.get(addr)
            if not pend or pend[0] != uuid or pend[2] != ns:
                return
            nc, name = pend[1], pend[4]
            try:
                info = json.loads(js.decode())
                want = min(MAX_WINDOWS, max(1, int(info.get("want", 1))))
                pref = [int(x) for x in info.get("pref", [])][:NSLOTS]
                create = bytes.fromhex(info["create"]) if info.get("create") else None
            except (ValueError, TypeError):
                return
            room = self.rooms.get(name.lower())
            pwkey = room.pwkey if room else create
            if pwkey is None or len(pwkey) != 32:
                return self.reject(addr, nc, "Room \"%s\" closed a moment ago. Enter it again to reopen it." % name)
            if not hmac.compare_digest(mac, hmac.new(pwkey, b"auth" + nc + ns + uuid + js, "sha256").digest()):
                return self.reject(addr, nc, "Wrong password for room \"%s\"." % name)
            if room is None:
                if len(self.rooms) >= self.MAX_ROOMS:
                    return self.reject(addr, nc, "The server has no space for another room.")
                room = self.rooms[name.lower()] = Room(name, pwkey)
                self.by_key[room.key] = room
                self.log.info("Room \"%s\" opened%s" % (name, " (with password)" if room.locked else ""))
            p = room.by_uuid.get(uuid)
            if (p is not None and addr != p.addr and now() - p.last_rx < 3.0
                    and int(info.get("epoch", 0) or 0) != p.epoch):
                self.log.warn("[%s] a second PC came in with %s's identity (copied h2link.json) and was refused"
                              % (room.name, p.name))
                return self.reject(addr, nc, DUPLICATE)
            used = set()
            for q in room.peers.values():
                if q.uuid != uuid:
                    used |= set(q.slots)
            if p is None:
                nid = next((i for i in range(1, NSLOTS + 1) if i not in room.peers), None)
                slots = alloc_slots(used, room.reserved, want, pref, uuid) if nid is not None else None
                if slots is None:
                    return self.reject(addr, nc, "Room \"%s\" is full: all 16 slots are taken." % name)
                p = Peer(nid)
                p.uuid, p.slots, p.want = uuid, slots, want
                p.epoch = random.getrandbits(32) | 1
                room.admitted += 1
                p.since = room.admitted
                room.peers[nid] = room.by_uuid[uuid] = p
                self.log.info("[%s] %s joined from %s:%d, slot %s" % (room.name, str(info.get("name", "?"))[:24], addr[0],
                                                                    addr[1], slot_text(slots)))
            else:
                if want != p.want or set(pref) != set(p.slots):
                    slots = alloc_slots(used, room.reserved, want, pref, uuid)
                    if slots is None:
                        return self.reject(addr, nc, "Room \"%s\" is full: all 16 slots are taken." % name)
                    p.slots, p.want = slots, want
                if int(info.get("epoch", 0)) != p.epoch:      # that PC's H2Link restarted
                    p.epoch = random.getrandbits(32) | 1
                    room.admitted += 1
                    p.since = room.admitted
                    p.tx.reset()
                    p.rx.reset()
            p.name = str(info.get("name", "?"))[:24]
            p.addr = p.pub = addr
            p.last_rx = now()
            p.lport = int(info.get("lport", 0) or 0)
            p.lan = [(str(a[0]), int(a[1])) for a in info.get("lan", [])[:6] if len(a) == 2]
            out = json.dumps(dict(id=p.id, key=room.key.hex(), epoch=p.epoch, hepoch=room.epoch, slots=p.slots,
                                  room=room.name, you=list(addr), since=p.since, server=True,
                                  relay=self.relay_only)).encode()
            mac = hmac.new(room.pwkey, b"welc" + nc + ns + out, "sha256").digest()
            self.send(HDR.pack(T_WELCOME, 0xFF, 0xFF, MAGIC) + nc + mac + out, addr)
            self.roster(room)


def query_rooms(text, timeout=1.5):
    """Ask a lobby server which rooms are open. Used by the control page."""
    hidden = text.strip().upper().startswith(KEY_PREFIX)
    try:
        host, port, hidden = server_target(text)
    except ValueError:
        return dict(ok=False, error=KEY_DAMAGED if hidden else "\"%s\" is not an address H2Link can use." % text)
    try:
        ip = socket.gethostbyname(host)
    except OSError:
        return dict(ok=False, error=KEY_NO_NAME if hidden else "The name \"%s\" cannot be looked up from this PC." % host)
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.settimeout(timeout)
        nonce = os.urandom(8)
        s.sendto(HDR.pack(T_LIST, 0xFF, 0xFF, MAGIC) + nonce + bytes(1100), (ip, port))
        end = time.time() + timeout
        while time.time() < end:
            data, _ = s.recvfrom(4096)
            if data[:1] == bytes([T_ROOMS]) and data[3:7] == MAGIC and data[7:15] == nonce:
                return dict(ok=True, rooms=json.loads(data[15:].decode()))
    except (OSError, ValueError):
        pass
    finally:
        s.close()
    return dict(ok=False, error="The server is not answering." if hidden else "The server at %s is not answering." % text)


# ===========================================================================
# Local web page (127.0.0.1 only) that drives the engine
# ===========================================================================
PAGE_HTML = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>H2Link</title><link rel="icon" href="/favicon.ico">
<style>
/* Look borrowed from the Halo 2 menus and pre-game lobby: deep blue glass panels with a title strip,
   pale blue type, a bright bar for the selected item, and the player list as one coloured bar per player.
   Drawn with CSS only: no game art, logos or fonts. */
:root{
  --ink:#dcebff; --muted:#8eb1dc; --line:rgba(118,172,240,.42); --hi:#9fd0ff; --glass:rgba(20,62,124,.50);
  --deep:rgba(6,20,46,.72); --sel1:#2c6fc0; --sel2:#63abf2; --relay:#ffc24f; --bad:#ff7d68;
  --face:Bahnschrift,"DIN Alternate","Segoe UI",system-ui,sans-serif;
}
*{box-sizing:border-box}
html{background:#030b18}
body{margin:0;min-height:100vh;color:var(--ink);font:15px/1.45 var(--face);font-variant-numeric:tabular-nums;
  background:radial-gradient(1100px 620px at 22% -8%,#1b4c91 0%,#0b2550 46%,rgba(4,13,29,0) 100%),
    radial-gradient(900px 520px at 105% 108%,#123a74 0%,rgba(4,13,29,0) 70%),#040d1d;background-attachment:fixed}
body::before{content:"";position:fixed;inset:0;pointer-events:none;
  background:repeating-linear-gradient(0deg,rgba(140,195,255,.035) 0 1px,transparent 1px 3px)}
.wrap{position:relative;max-width:1240px;margin:0 auto;padding:20px 20px 16px;display:grid;
  grid-template-columns:1fr;gap:20px}
header{grid-column:1/-1;display:flex;align-items:center;justify-content:space-between;gap:16px;flex-wrap:wrap;
  padding:0 0 12px;border-bottom:1px solid var(--line);
  border-image:linear-gradient(90deg,var(--hi),rgba(118,172,240,.15)) 1}
h1 img.logo{height:22px;width:auto;vertical-align:-2px;display:inline-block;filter:drop-shadow(0 0 9px rgba(110,180,255,.55))}
h1{margin:0;font-size:30px;font-weight:700;font-stretch:75%;letter-spacing:.14em;text-transform:uppercase;color:#fff;
  text-shadow:0 0 18px rgba(110,180,255,.55)}
h1 small{font-size:13px;font-weight:400;font-stretch:100%;letter-spacing:.04em;text-transform:none;color:var(--muted);margin-left:12px;text-shadow:none}
#status{font-size:14px;letter-spacing:.08em;text-transform:uppercase;color:var(--hi);padding:5px 12px;
  border:1px solid var(--line);background:var(--deep)}
/* three columns of equal height; the lobby adds a chat across all three */
/* main menu: settings | room list | activity.  room: game settings | chat | players, activity across the bottom */
.cols{display:grid;grid-template-columns:minmax(0,1.15fr) minmax(0,1fr) minmax(290px,1fr);gap:20px;align-items:stretch;
  grid-template-areas:"left mid act"}
.cols.inroom{grid-template-areas:"left chat players" "act act act"}
.cols>.panel{display:flex;flex-direction:column;min-width:0}
#p-left{grid-area:left} #mid-servers{grid-area:mid} #chat{grid-area:chat;min-height:420px} #mid-players{grid-area:players}
#p-act{grid-area:act} .cols.inroom #p-act{height:max(204px,calc(100vh - 690px))}
@media (min-width:1001px){.cols.inroom #p-left{contain:size;overflow-y:auto}}
#room-player h3.sub{margin-top:0}
/* a tick box beside a menu: as tall as the menu and centred on it, its text centred */
.row .check.beside{align-self:flex-end;height:var(--ctl,38px);margin:0 0 var(--ctl-mb,0px)!important;padding:0;justify-content:flex-start}
.row .check.beside{gap:10px}
.row .check.beside span{text-align:left;line-height:1.25;flex:0 1 auto;white-space:nowrap}
.cols.inroom #p-left .row .check.beside{--ctl:34px;--ctl-mb:5px}
/* the room's game settings: tighter, so Launch and Leave room stay in view */
.cols.inroom #p-left label{margin-bottom:5px}
.cols.inroom #p-left label.check{margin-bottom:5px!important}
.cols.inroom #p-left input,.cols.inroom #p-left select{padding:6px 8px;margin-top:3px}
.cols.inroom #p-left h3.sub{margin:8px 0 4px}
.cols.inroom #p-left .hint{margin:1px 0 4px;font-size:12.5px;line-height:1.35}
.cols.inroom #p-left #t-game{margin:0 0 6px!important}
.cols.inroom #p-left #plan{margin-bottom:4px!important}
.cols.inroom #p-left #plan .row{margin-top:4px!important}
.cols.inroom #p-left #d-skulls{margin-top:4px!important}
.cols.inroom #p-left #room-player{margin-bottom:6px!important}
.cols.inroom #p-left .roominfo{margin-bottom:6px}
.cols.inroom #log{height:auto;flex:1 1 0;min-height:0}
/* in a room the activity box is low and wide: the report button sits beside the list, not under it */
.cols.inroom #p-act{display:grid;grid-template-columns:minmax(0,1fr) 300px;grid-template-rows:auto auto 1fr;column-gap:24px;
  grid-template-areas:"h h" "log hint" "log btn"}
.cols.inroom #p-act>h2{grid-area:h} .cols.inroom #p-act>#log{grid-area:log}
.cols.inroom #p-act>p{grid-area:hint;margin:0 0 10px!important} .cols.inroom #p-act>button{grid-area:btn;align-self:start;justify-self:start}
#chatlog{flex:1 1 0;min-height:0;overflow:auto;margin:0;padding:0;list-style:none;font-size:14.5px;line-height:1.5;
  scrollbar-color:var(--sel1) transparent}
#chatlog li{padding:1px 0;overflow-wrap:anywhere} #chatlog b{color:var(--hi);font-weight:600;margin-right:6px}
#chatlog li.mine b{color:#fff} #chatlog time{color:var(--muted);font-size:12.5px;margin-right:8px}
.chat .row{margin-top:10px;flex-wrap:nowrap} .chat .row input{margin:0}
h3.sub{margin:18px 0 10px;font-size:13px;font-weight:600;letter-spacing:.12em;text-transform:uppercase;color:var(--hi)}
.err{transition:opacity 1s} .err.fade{opacity:0}
.panel{background:linear-gradient(180deg,rgba(34,86,160,.55),var(--glass) 120px,rgba(10,34,78,.62));
  border:1px solid var(--line);box-shadow:inset 0 0 0 1px rgba(170,212,255,.07),0 0 28px rgba(18,78,180,.22);
  padding:0 16px 18px}
h2{margin:0 -16px 14px;padding:9px 16px 8px;font-size:15px;font-weight:600;font-stretch:90%;letter-spacing:.14em;
  text-transform:uppercase;color:#fff;background:linear-gradient(90deg,rgba(99,171,242,.38),rgba(99,171,242,.06));
  border-bottom:1px solid var(--line)}
.split{margin:18px -16px 0;padding:0 16px}
.split>h2{border-top:1px solid var(--line)}
details.split{border-top:1px solid var(--line);padding-top:12px}
/* player list */
.roster h2{display:flex;justify-content:space-between} .roster h2 span{color:var(--hi);letter-spacing:.06em}
.rack{display:grid;gap:4px}
.cell{--c:#3b6db3;display:grid;grid-template-columns:30px minmax(0,1fr) auto 22px;align-items:center;column-gap:8px;height:25px;padding-right:6px;
  padding-right:9px;border:1px solid rgba(255,255,255,.16);
  background:linear-gradient(90deg,color-mix(in srgb,var(--c) 74%,#051022),color-mix(in srgb,var(--c) 34%,#051022))}
.cell .num{height:100%;display:grid;place-items:center;font-size:15px;font-weight:700;font-stretch:75%;color:#fff;
  background:color-mix(in srgb,var(--c) 88%,#000);border-right:1px solid rgba(255,255,255,.22);text-shadow:0 1px 2px rgba(0,0,0,.6)}
.cell .who{font-weight:600;color:#fff;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;text-shadow:0 1px 2px rgba(0,0,0,.55)}
.cell .how{font-size:12px;color:rgba(255,255,255,.86);white-space:nowrap;text-align:right;line-height:1}
.cell .how i{font-style:normal;display:block}
.cell.open{background:rgba(8,26,58,.45);border-color:rgba(118,172,240,.16)}
.cell.open .num{background:transparent;border-right-color:rgba(118,172,240,.16);color:rgba(142,177,220,.5)}
.cell.open .who{font-weight:400;color:rgba(142,177,220,.5);text-shadow:none}
.cell.you{border-color:#fff;box-shadow:0 0 0 1px #fff,0 0 14px rgba(150,205,255,.6)}
.sig{display:inline-flex;align-items:flex-end;gap:2px;height:14px;width:22px}
.sig i{display:block;width:3px;background:rgba(255,255,255,.22);border-radius:1px}
.sig i:nth-child(1){height:4px}.sig i:nth-child(2){height:7px}.sig i:nth-child(3){height:10px}.sig i:nth-child(4){height:14px}
.sig.b1 i:nth-child(-n+1){background:#ff5a5a} .sig.b2 i:nth-child(-n+2){background:#ffd24a}
.sig.b3 i:nth-child(-n+3),.sig.b4 i:nth-child(-n+4){background:#7dff9a} .sig.b0 i:nth-child(1){background:#ff5a5a}
.sig.me i{background:rgba(255,255,255,.55)!important}
.hosttag{font-style:normal;font-size:10.5px;font-weight:700;letter-spacing:.06em;text-transform:uppercase;margin-left:8px;
  padding:1px 5px;border:1px solid rgba(255,255,255,.55);border-radius:3px;color:#fff;vertical-align:1px}
.roominfo{margin:0 0 12px;padding:10px 12px;border:1px solid var(--line);background:rgba(4,16,38,.45)}
.roominfo .ri-host{margin:0 0 6px;color:var(--muted)} .roominfo .ri-host b{color:#fff}
.roominfo dl{display:grid;grid-template-columns:max-content minmax(0,1fr) max-content minmax(0,1fr);gap:4px 12px;margin:0}
.roominfo dd.wide{grid-column:2/-1}
.roominfo dt{color:var(--muted)} .roominfo dd{margin:0;color:#fff;font-weight:600}
/* form */
label{display:block;margin:0 0 12px;font-size:13px;letter-spacing:.03em;color:var(--muted)}
input,select{display:block;width:100%;margin-top:4px;padding:8px 9px;font:15px var(--face);color:#fff;
  background:var(--deep);border:1px solid var(--line);border-radius:0}
select{background-color:#0a1d3c} select:disabled{opacity:.55}
body.gone .cols{opacity:.35;pointer-events:none}
label.check{display:flex;align-items:center;gap:8px;margin:0;font-size:14px;color:var(--ink);cursor:pointer}
label.check input{width:16px;height:16px;margin:0;padding:0;accent-color:var(--sel2);flex:none}
label.check input:disabled+span,label.check:has(input:disabled){opacity:.6;cursor:default}
#skulls h3{margin:10px 0 6px;font-size:13px;font-weight:600;letter-spacing:.1em;text-transform:uppercase;color:var(--muted)}
#skulls .sk{display:grid;grid-template-columns:1fr 1fr;gap:5px 12px}
select:focus{outline:none;border-color:var(--hi);box-shadow:0 0 0 1px var(--hi),0 0 12px rgba(110,180,255,.35)}
input::placeholder{color:rgba(142,177,220,.6)}
input:focus{outline:none;border-color:var(--hi);box-shadow:0 0 0 1px var(--hi),0 0 12px rgba(110,180,255,.35)}
.hint{font-size:13px;color:var(--muted);margin:-6px 0 12px}
button{font:600 14px var(--face);letter-spacing:.1em;text-transform:uppercase;padding:10px 18px;border:0;cursor:pointer;color:#fff;
  background:linear-gradient(90deg,var(--sel1),var(--sel2));text-shadow:0 1px 2px rgba(0,0,0,.45);
  clip-path:polygon(9px 0,100% 0,100% calc(100% - 9px),calc(100% - 9px) 100%,0 100%,0 9px)}
button:hover:not(:disabled){filter:brightness(1.18)}
button.quiet{background:linear-gradient(90deg,rgba(44,111,192,.42),rgba(44,111,192,.2));color:var(--ink)}
button:disabled{opacity:.45;cursor:default}
button:focus-visible,summary:focus-visible{outline:2px solid #fff;outline-offset:-4px}
.row{display:flex;gap:10px;align-items:end;flex-wrap:wrap}
.row label{flex:1;margin-bottom:0;min-width:150px}
details{margin:2px 0 14px} summary{cursor:pointer;color:var(--hi);font-size:13px;letter-spacing:.08em;text-transform:uppercase;margin-bottom:10px}
.big{font-size:21px;font-weight:600;font-stretch:85%;letter-spacing:.04em;color:#fff;margin:0 0 4px}
.warn{border-left:3px solid var(--relay);padding:8px 12px;margin:12px 0;background:var(--deep)}
.err{border-left:3px solid var(--bad);padding:8px 12px;margin:14px 0 0;background:var(--deep);color:#ffd9d2}
#log{flex:1 1 0;min-height:260px;overflow:auto;font-size:13.5px;line-height:1.5;margin:0;padding:0;list-style:none;scrollbar-color:var(--sel1) transparent}
#log li{padding:1px 0 1px 70px;text-indent:-70px;overflow-wrap:anywhere}
#log time{display:inline-block;width:70px;text-indent:0;color:var(--muted)}
#log li.warn2{color:var(--relay)} #log li.error{color:var(--bad)}
.facts{margin:10px 0 0;padding:0;list-style:none} .facts li{margin:3px 0}
/* room list: menu rows, the picked one lit like a selected menu item */
.rooms{margin:0 0 12px;font-size:14px;color:var(--muted)}
.rooms button{display:flex;justify-content:space-between;gap:12px;width:100%;margin:0 0 4px;padding:8px 12px;clip-path:none;
  background:var(--deep);border:1px solid var(--line);border-left:3px solid var(--sel2);color:var(--ink);
  font-size:15px;letter-spacing:.02em;text-transform:none;text-align:left}
.rooms button span{font-weight:400;color:var(--muted);white-space:nowrap}
.rooms button[aria-pressed=true]{background:linear-gradient(90deg,var(--sel1),var(--sel2));border-color:#fff;color:#fff}
.rooms button[aria-pressed=true] span{color:#fff}
/* the crash notice: like the update notice */
#crash{margin:-20px 0 0;color:var(--ink);font-size:14px}
#crash #t-crash{min-height:20px;line-height:20px;border-bottom:1px solid var(--line);padding-bottom:1px}
#crash #t-crash a,#p-act .hint a{color:#9cd2ff}
#crash .upd-row{display:flex;align-items:center;gap:18px;margin-top:20px} #crash #a-crashno{color:#9cd2ff;font-size:13px;text-decoration:none;letter-spacing:.04em}
#upd:not([hidden])+#crash{margin-top:0}
/* the update notice: one band under the header line, closed by a line of its own */
/* the text sits in the page's usual 20 px gap under the header line, centred, closed by a second line; the
   button keeps its place and size under that line */
#upd{margin:-20px 0 0;color:var(--ink);font-size:14px}       /* the page's 20 px gap follows below */
#upd #t-upd{height:20px;line-height:20px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;
  border-bottom:1px solid var(--line)} #upd #t-upd b{color:#fff;font-weight:700}
#upd .upd-row{display:flex;align-items:center;gap:18px;margin-top:20px}   /* = the gap between the columns */
.share{border-top:1px solid var(--line);margin:14px 0 4px;padding-top:12px;color:var(--muted);font-size:14px}
.share output{flex:1;min-width:180px;font-size:21px;font-weight:600;font-stretch:85%;color:#fff;user-select:all}
[hidden]{display:none!important}
#a-upd{color:#9cd2ff;text-decoration:none;letter-spacing:.04em}#a-upd:hover{text-decoration:underline}
@media (max-width:1000px){.cols{grid-template-columns:1fr;grid-template-areas:"left" "mid" "act"}.cols.inroom{grid-template-areas:"left" "players" "chat" "act"}.rack{grid-template-columns:1fr 1fr}#log{flex:none;height:300px}}
@media (max-width:700px){.rack{grid-template-columns:1fr}}
@media (prefers-reduced-motion:no-preference){.cell.you{animation:lit 2.6s ease-in-out infinite}
  @keyframes lit{50%{box-shadow:0 0 0 1px #fff,0 0 22px rgba(150,205,255,.95)}}}
</style></head><body><div class="wrap">
<header><h1><img class="logo" alt="H2Link" src="data:image/png;base64,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"><small id="ver"></small></h1><div class="row" style="flex:none;align-items:center;gap:10px">
  <div id="status" role="status">Starting</div><button class="ghost" id="b-quit" style="flex:none;padding:8px 14px">Close H2Link</button></div></header>

<div id="upd" hidden><div id="t-upd"></div>
  <div class="upd-row"><button id="b-upd">Install update</button><a id="a-upd" target="_blank" rel="noopener">What's new</a></div></div>
<div id="crash" hidden><div id="t-crash">The game closed because of a crash. Would you like to report it? Open an issue at
  <a href="#" id="a-issues">github.com/Fortune090/H2Link/issues/new</a> and attach the crash report.</div>
  <div class="upd-row"><button id="b-crashview">View report</button><a href="#" id="a-crashno">Dismiss</a></div></div>
<div class="cols" id="cols">
<section class="panel" id="p-left">
  <div id="v-idle">
    <h2>Settings</h2>
    <label>H2Link Player Name<input id="f-name" maxlength="24" autocomplete="off"></label>
    <div id="idle-player"><div id="player-box">
    <h3 class="sub">Player settings</h3>
    <input type="checkbox" id="f-skip" checked hidden>
    <label class="check" id="l-autostart" style="margin:0 0 12px" hidden><input type="checkbox" id="f-autostart">Start my game when the room host launches</label>
    <div id="profile-box">
      <label>Halo 2 profile to sign in with<input id="f-profile" maxlength="16" autocomplete="off" spellcheck="false" placeholder="Guest profile"></label>
      <p class="hint" id="t-profile"></p>
      <button class="quiet" id="b-useprofile" style="text-transform:none;letter-spacing:.02em;margin-bottom:6px" hidden></button>
    </div>
    <div class="row" style="align-items:flex-end">
      <label>Players on this PC<select id="f-want"><option>1</option><option>2</option><option>3</option><option>4</option></select></label>
      <label class="check beside" title="Without title bars. 1 window: full screen. 2: left and right. 3: one on top, two below (on 21:9 and wider: one left, two right). 4: the four corners."><input type="checkbox" id="f-snap"><span>Auto split screen</span></label>
    </div>
    </div></div>
    <details style="margin-top:14px"><summary>Other H2Link settings</summary>
      <label>Game folder<input id="f-dir" placeholder="C:\Games\H2EK" autocomplete="off" spellcheck="false"></label>
      <label id="l-server">Lobby Server<input id="f-server" placeholder="Server key or address" autocomplete="off" spellcheck="false"></label>
      <label>UDP port of this PC<input id="f-port" type="number" min="1" max="65535"></label>
      <label>Exe name, if the folder holds several<input id="f-exe" autocomplete="off" spellcheck="false"></label>
      <label>Extra launch arguments<input id="f-args" autocomplete="off" spellcheck="false"></label>
    </details>
    <div class="split">
      <h2>Create/Join Room</h2>
      <div class="row"><label>Room name<input id="f-room" maxlength="32" autocomplete="off"></label>
        <label>Password, if any<input id="f-pw" autocomplete="off"></label></div>
      <div style="height:14px"></div>
      <button id="b-enter">Create room</button>
    </div>
    <details class="split" id="d-direct"><summary>Direct link play</summary>
      <p class="hint" style="margin-top:0">One player hosts on their own PC and gives the others its IP address. The password above applies.</p>
      <div class="row"><label>Host IP address<input id="f-addr" autocomplete="off" spellcheck="false"></label>
      <button class="quiet" id="b-join">Join room</button></div>
      <p class="hint" style="margin:16px 0 10px">Hosting asks your router to open UDP port <span id="t-port">31100</span>. If the router refuses, forward that port to this PC by hand.</p>
      <button class="quiet" id="b-host">Host a room on this PC</button>
    </details>
  </div>

  <div id="v-conn" hidden>
    <h2>Joining</h2>
    <p id="t-conn"></p>
    <button class="quiet" id="b-cancel">Cancel</button>
  </div>

  <div id="v-room" hidden>
    <h2>Game settings</h2>
    <p id="t-game" style="margin:0 0 14px"></p>
    <div id="roominfo" class="roominfo" hidden></div>
    <div id="plan" style="margin-bottom:14px" hidden>
      <div class="row"><label>Level<select id="f-level"></select></label>
        <label>Difficulty<select id="f-diff"></select></label></div>
      <div class="row" style="margin-top:12px"><label>Tick rate<select id="f-tick"></select></label>
        <label class="check beside"><input type="checkbox" id="f-cheats"><span>Debug menu/cheats</span></label></div>
      <details id="d-skulls" style="margin:12px 0 0"><summary id="t-skulls">Skulls</summary><div id="skulls"></div></details>
    </div>
    <div id="room-player" style="margin-bottom:14px"></div>
    <div class="row" style="margin-bottom:6px"><button id="b-launch">Start the game</button>
      <button class="quiet" id="b-leave">Leave room</button></div>
    <div id="share" class="share" hidden><div>Address to give to the other players</div>
      <div class="row"><output id="t-share"></output><button class="quiet" id="b-copy">Copy address</button></div></div>
    <div id="warns"></div>
    <ul class="facts" id="facts"></ul>
  </div>
  <div id="err" class="err" hidden></div>
</section>

<section class="panel" id="mid-servers">
  <h2>Room list</h2>
  <div id="rooms" class="rooms" aria-live="polite"></div>
  <p class="hint" id="t-roomhint" style="margin:0">Click a room to join it.</p>
</section>

<aside class="panel roster" id="mid-players" hidden><h2>Players<span id="t-count"></span></h2>
  <div class="rack" id="rack" aria-label="The 16 player slots of the lobby"></div></aside>

<section class="panel" id="p-act">
  <h2>Session activity</h2>
  <ul id="log" aria-live="polite"></ul>
  <p class="hint" style="margin:12px 0 10px">A report is one zip with this list and the game's own logs for your slot. When something goes wrong, open an issue at <a href="#" class="issues">github.com/Fortune090/H2Link/issues/new</a> and attach it.</p>
  <button class="quiet" id="b-report" style="align-self:flex-start">Save a report</button>
</section>

<section class="panel chat" id="chat" hidden>
  <h2>Room chat</h2>
  <ul id="chatlog" aria-live="polite"></ul>
  <div class="row"><input id="f-chat" maxlength="300" autocomplete="off" aria-label="Message to the room"><button id="b-chat" style="flex:none">Send</button></div>
</section>
</div>
</div>
<script>
const TOKEN="__TOKEN__";let S=null,filled=false,lastLog=0;
const $=id=>document.getElementById(id);
const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const two=n=>String(n).padStart(2,'0');
function post(cmd,body){return fetch('/api/'+cmd,{method:'POST',headers:{'Content-Type':'application/json','X-H2Link':TOKEN},body:JSON.stringify(body||{})}).then(tick)}
const DIRECT_PORT=31100;
function hostAddr(){const v=$('f-addr').value.trim();return !v||/:\d+$/.test(v)?v:v+':'+DIRECT_PORT}
function form(){return{name:$('f-name').value,game_dir:$('f-dir').value,password:$('f-pw').value,port:$('f-port').value,
  want:$('f-want').value,exe:$('f-exe').value,args:$('f-args').value,address:hostAddr(),skip_picker:true,
  profile:$('f-profile').value,
  server:$('f-server').value,room:$('f-room').value}}
const srv=()=>$('f-server').value.trim()||(S&&S.cfg.builtin?'@builtin':'');
let roomsFor='',roomsBusy=false,roomNames=[];
function enterLabel(){const n=$('f-room').value.trim().replace(/\s+/g,' ').toLowerCase();
  $('b-enter').textContent=roomNames.includes(n)?'Join room':'Create room'}
function rooms(){
  const v=srv(),el=$('rooms');
  if(!S||S.mode!=='idle'||roomsBusy)return;
  if(!v){el.textContent='No lobby server set. Add your group\'s server key under Other H2Link settings.';$('t-roomhint').hidden=true;return}
  roomsBusy=true;
  fetch('/api/rooms?server='+encodeURIComponent(v)).then(r=>r.json()).then(o=>{roomsBusy=false;
    if(srv()!==v)return;
    roomNames=o.ok?o.rooms.map(r=>r.name.toLowerCase()):[];enterLabel();
    $('t-roomhint').hidden=!(o.ok&&o.rooms.length);
    if(!o.ok){el.textContent=o.error;return}
    if(!o.rooms.length){el.textContent='No rooms yet. Type a room name under Create/Join Room to create one.';return}
    const cur=$('f-room').value.trim().toLowerCase();
    el.innerHTML=o.rooms.map(r=>`<button type="button" title="Join ${esc(r.name)}" data-name="${esc(r.name)}" data-locked="${r.locked?1:''}" aria-pressed="${r.name.toLowerCase()===cur}">${esc(r.name)}<span>${r.locked?'password · ':''}(${r.players}/16)</span></button>`).join('')
  }).catch(()=>{roomsBusy=false})}
const TINT=['#b23a31','#2f66c4','#3e9440','#d5801f','#7446b0','#cfa72a','#8a5632','#cf6596',
  '#aeb9c4','#5d7389','#1f9694','#8f9f3c','#84222f','#35a6da','#b99b6b','#5157ab'];
function rack(){
  $('t-count').textContent=S.mode==='idle'?'':S.players+'/16';
  // S.slots comes in display order: the room host's PC first, each PC's windows together, open slots last.
  // Rows are numbered by position; a row whose game runs in another slot says so on hover.
  $('rack').innerHTML=S.slots.map((c,i)=>{
    let cls='open',who='Open',game='',bars='',tip='',host='';
    if(c.state==='you'){cls='you';who=esc(c.name);tip='This PC';bars=4}
    else if(c.state==='player'){cls=c.link;who=esc(c.name);
      bars=c.link==='silent'?0:c.ms==null?1:c.ms<40?4:c.ms<80?3:c.ms<150?2:1;
      tip=c.link==='silent'?'Not answering':(c.ms==null?'':c.ms+' ms, ')+c.link}
    if(c.state!=='open'){game=c.game?'Game running':'No game yet';if(c.host)host='<em class="hosttag">Host</em>'}
    const real=c.slot===i?'':` title="Game slot ${two(c.slot+1)}"`;
    const meter=c.state==='open'?'<span class="sig"></span>':`<span class="sig b${bars}${c.state==='you'?' me':''}" title="${esc(tip)}"><i></i><i></i><i></i><i></i></span>`;
    return `<div class="cell ${cls}"${c.state==='open'?'':` style="--c:${TINT[i]}"`}><span class="num"${real}>${two(i+1)}</span><span class="who" title="${who}">${who}${host}</span><span class="how">${game}</span>${meter}</div>`}).join('')}
function player(){
  const on=true,name=$('f-profile').value.trim(),seen=S.seen_profile||'';
  $('profile-box').hidden=false;
  $('t-profile').textContent=name?'The game signs you in as "'+name+'". If you have no Halo 2 profile with that name, you play under your H2Link name, with the game\'s default controls.':
    'Empty: you play under your H2Link name, with the game\'s default controls.';
  const offer=on&&seen&&seen!==name;
  $('b-useprofile').hidden=!offer;
  if(offer)$('b-useprofile').textContent='Use "'+seen+'", last used in the game on this PC'}
function updateBanner(){
  const u=S.update;$('upd').hidden=!u;if(!u)return;
  $('t-upd').innerHTML='New version available: <b>'+esc(u.newer_app?'v'+u.version:'game exe v'+u.exe)+
    '</b>. Everyone in a Room should be using the same version.';
  $('a-upd').href=u.page;$('b-upd').hidden=!u.installer;
  const st=u.status||'';$('b-upd').disabled=st==='downloading'||st==='installing';
  $('b-upd').textContent=st==='downloading'?'Downloading...':st==='installing'?'Installing...':st==='failed'?'Try again':'Install update';
  if(st==='installing')$('t-upd').innerHTML='Installing <b>v'+esc(u.version)+'</b>. H2Link closes now and starts again in a moment.'}
function crashNotice(){const c=S.crash;$('crash').hidden=!c}
function panel(){
  updateBanner();crashNotice();
  player();
  const idle=S.mode==='idle',conn=S.state==='connecting';
  $('v-idle').hidden=!idle;$('v-conn').hidden=!conn;$('v-room').hidden=idle||conn;
  // Player settings live in the main menu, and in a room under the game settings: the same controls, moved.
  const pb=$('player-box'),home=$(idle||conn?'idle-player':'room-player');
  $('l-autostart').hidden=idle||conn||!!S.i_host;   // only for a client in a room
  if(pb.parentNode!==home)home.appendChild(pb);
  $('mid-servers').hidden=!idle;$('mid-players').hidden=idle;$('chat').hidden=idle||conn;
  $('cols').classList.toggle('inroom',!idle&&!conn);
  showErr(S.error);
  $('t-port').textContent=$('f-port').value||S.cfg.port;
  if(conn)$('t-conn').textContent='Contacting the '+(S.on_server?'server':'host')+(S.host?' at '+S.host:'')+'.';
  if(!idle&&!conn){
    const n=S.my_slots.length,run=S.games.length,auto=S.exe_ver>=S.auto_exe,P=S.plan;
    $('plan').hidden=!(S.i_host&&auto);
    if(S.i_host&&auto){
      if(!$('f-level').options.length){
        $('f-level').innerHTML=S.levels.map(l=>`<option value="${l[0]}">${esc(l[1])}</option>`).join('');
        $('f-diff').innerHTML=S.difficulties.map((x,i)=>`<option value="${i}">${esc(x)}</option>`).join('');
        $('f-tick').innerHTML=S.ticks.map(t=>`<option value="${t[0]}">${esc(t[1])}</option>`).join('');
        $('skulls').innerHTML=S.skulls.map(g=>`<h3>${esc(g[0])}</h3><div class="sk">`+g[1].map(k=>
          `<label class="check"><input type="checkbox" data-skull="${k[0]}">${esc(k[1])}</label>`).join('')+'</div>').join('')}
      if(Date.now()>planHold){
        if(document.activeElement!==$('f-level'))$('f-level').value=P.level;
        if(document.activeElement!==$('f-diff'))$('f-diff').value=P.diff;
        if(document.activeElement!==$('f-tick'))$('f-tick').value=P.tick;
        $('f-cheats').checked=P.cheats;
        document.querySelectorAll('#skulls input').forEach(i=>{i.checked=P.skulls.includes(i.dataset.skull)})}
      document.querySelectorAll('#plan select,#plan input').forEach(i=>{i.disabled=run>0});
      $('t-skulls').textContent=P.skulls.length?'Skulls, '+P.skulls.length+' on':'Skulls, none on'}
    const waiting=!S.i_host&&!P.known;
    $('t-game').textContent=!auto?(run===0?'Start the game now. It takes your slot because every other slot is held.':'The game is running in your slot.'):
      S.i_host?(run===0?'You are the room host.':
        'Your game is running. Players who start now join in progress. Close the game to change these.'):
      run>0?'The game is running in your slot.':
      waiting?'Waiting for the room host\'s settings.':
      S.launch_wait?'Waiting for '+S.host_name+'\'s level to finish loading. Your game starts by itself then.':
'';
    $('roominfo').hidden=S.i_host||waiting;
    if(!S.i_host&&!waiting){
      const L=Object.fromEntries(S.levels.map(l=>[String(l[0]),l[1]])),T=Object.fromEntries(S.ticks.map(t=>[String(t[0]),t[1]]));
      const SK=Object.fromEntries(S.skulls.flatMap(g=>g[1]));
      const row=(k,v)=>`<dt>${k}</dt><dd>${esc(v)}</dd>`;
      $('roominfo').innerHTML=`<dl><dt>Host</dt><dd class="wide">${esc(S.host_name)}</dd>`+
        row('Level',L[String(P.level)]||P.level)+row('Difficulty',S.difficulties[P.diff]||'')+
        row('Tick rate',T[String(P.tick)]||P.tick)+row('Cheats',P.cheats?'On':'Off')+
        `<dt>Skulls</dt><dd class="wide">${esc(P.skulls.length?P.skulls.map(k=>SK[k]||k).join(', '):'None')}</dd></dl>`}
    $('t-game').hidden=!$('t-game').textContent;
    const early=!S.i_host&&run===0&&!S.host_started;   // a client before the room host has launched
    $('b-launch').disabled=run>=n||waiting||early;
    $('b-launch').textContent=run>0&&run<n?'Start another game window':(S.i_host&&auto?'Launch':S.launch_wait?'Start now anyway':'Start the game');
    $('b-leave').textContent=S.mode==='host'?'Close room':'Leave room';
    $('warns').innerHTML=S.warnings.map(w=>`<div class="warn">${esc(w)}</div>`).join('');
    const f=[];
    $('share').hidden=!(S.mode==='host'&&S.share);$('t-share').textContent=S.share||'';
    if(S.mode==='host'){
      if(!S.share)f.push('Players join with your public IP address and port '+S.port+'.');
      f.push(S.router==='open'?'The router forwards UDP port '+S.port+' to this PC.':
        S.router==='closed'?'The router did not open UDP port '+S.port+'. Forward it to this PC by hand.':
        'Asking the router to open UDP port '+S.port+'.');
      if(S.lan.length)f.push('On your own network players can use '+S.lan.map(a=>a+(S.port===31100?'':':'+S.port)).join(' or ')+'.')}
    if(!S.exe)f.push('No game exe found in the game folder yet.');
    if(S.exe&&!auto)f.push('This exe is older than v'+S.auto_exe+', so the level is not started for you. Use the game\'s menus.');
    if(S.exe&&auto&&!S.have_tick.includes(S.plan.tick))f.push('The room plays at '+S.plan.tick+' tick and this game folder has no '+S.plan.tick+'-tick exe yet.');
    $('facts').innerHTML=f.map(x=>`<li>${esc(x)}</li>`).join('')}
  $('status').textContent=idle?'Not in a room':conn?'Joining':S.state==='reconnecting'?'Reconnecting to '+S.room:
    'In room: '+S.room+', '+S.players+' player'+(S.players===1?'':'s')}
// an error shows for 10 s, fading out over the last one; it shows again when it happens again
let errText=null,errAt=0;
function showErr(e){const el=$('err');
  if(e&&e!==errText){errAt=Date.now();el.textContent=e;el.classList.remove('fade')}
  errText=e||null;const age=Date.now()-errAt;
  el.hidden=!e||age>10000;el.classList.toggle('fade',age>9000)}
let lastChat=0;
function chat(){const el=$('chatlog'),c=S.chat||[];
  if(!c.length||c[c.length-1][0]<lastChat){if(lastChat){el.innerHTML='';lastChat=0}if(!c.length)return}
  const stick=el.scrollTop+el.clientHeight>=el.scrollHeight-8,fresh=c.filter(m=>m[0]>lastChat);if(!fresh.length)return;
  lastChat=fresh[fresh.length-1][0];
  el.insertAdjacentHTML('beforeend',fresh.map(m=>{const d=new Date(m[1]*1000);
    return `<li${m[4]?' class="mine"':''}><time>${two(d.getHours())}:${two(d.getMinutes())}</time><b>${esc(m[2])}</b>${esc(m[3])}</li>`}).join(''));
  if(stick||fresh.some(m=>m[4]))el.scrollTop=el.scrollHeight}
const sendChat=()=>{const t=$('f-chat').value.trim();if(!t)return;$('f-chat').value='';post('chat',{text:t})};
function log(){
  const el=$('log'),stick=el.scrollTop+el.clientHeight>=el.scrollHeight-8;
  const fresh=S.log.filter(l=>l[0]>lastLog);if(!fresh.length)return;lastLog=fresh[fresh.length-1][0];
  el.insertAdjacentHTML('beforeend',fresh.map(l=>{const d=new Date(l[1]*1000);
    return `<li class="${l[2]==='warn'?'warn2':l[2]}"><time>${two(d.getHours())}:${two(d.getMinutes())}:${two(d.getSeconds())}</time>${esc(l[3])}</li>`}).join(''));
  while(el.children.length>400)el.removeChild(el.firstChild);
  if(stick)el.scrollTop=el.scrollHeight}
function tick(){return fetch('/api/state').then(r=>r.json()).then(s=>{S=s;
  if(!filled){filled=true;const c=s.cfg;$('f-name').value=c.name;$('f-dir').value=c.game_dir;$('f-pw').value=c.password;
    $('f-port').value=c.port;$('f-want').value=c.want;$('f-exe').value=c.exe;$('f-args').value=c.args;$('f-addr').value=(c.address||'').replace(/:31100$/,'');$('f-skip').checked=c.skip_picker;$('f-autostart').checked=c.auto_start;$('f-snap').checked=c.snap_windows;
    $('f-profile').value=c.profile;
    $('f-server').value=c.server;$('f-room').value=c.room;$('d-direct').open=!c.server&&!c.builtin;
    if(c.builtin)$('f-server').placeholder='Built in. Paste another key to change it.';enterLabel();rooms();
    $('ver').textContent='version '+s.version}
  rack();panel();log();chat()}).catch(()=>{$('status').textContent=closed?'H2Link is closed':'H2Link is not running';
    $('b-quit').hidden=true;document.body.classList.add('gone')})}
$('b-host').onclick=()=>post('host',form());
$('b-enter').onclick=()=>post('join',Object.assign(form(),{via:'server'}));
// a click on a room joins it; a room with a password asks for it first
$('rooms').onclick=e=>{const b=e.target.closest('button');if(!b)return;$('f-room').value=b.dataset.name;
  [...$('rooms').children].forEach(x=>x.setAttribute('aria-pressed',x===b));enterLabel();
  if(b.dataset.locked&&!$('f-pw').value){$('t-roomhint').textContent='"'+b.dataset.name+'" has a password. Type it under Create/Join Room and press Join room.';
    $('f-pw').focus();return}
  $('t-roomhint').textContent='Click a room to join it.';
  post('join',Object.assign(form(),{via:'server'}))};
$('f-room').addEventListener('input',enterLabel);
$('f-server').addEventListener('change',rooms);
$('f-room').addEventListener('keydown',e=>{if(e.key==='Enter')$('b-enter').click()});
$('f-pw').addEventListener('keydown',e=>{if(e.key==='Enter')$('b-enter').click()});
setInterval(rooms,4000);
$('b-join').onclick=()=>post('join',form());
$('b-cancel').onclick=()=>post('leave');
$('b-leave').onclick=()=>post('leave');
$('b-launch').onclick=()=>post('launch');
const savePlayer=()=>{post('settings',{skip_picker:true,auto_start:$('f-autostart').checked,profile:$('f-profile').value});if(S)player()};
$('f-want').onchange=()=>post('settings',{want:+$('f-want').value});
$('f-snap').onchange=()=>post('settings',{snap_windows:$('f-snap').checked});
$('f-skip').onchange=savePlayer;$('f-autostart').onchange=savePlayer;$('f-profile').onchange=savePlayer;$('f-profile').oninput=()=>{if(S)player()};
$('b-useprofile').onclick=()=>{$('f-profile').value=S.seen_profile;savePlayer()};
let closed=false;
$('b-upd').onclick=()=>post('update');
$('b-crashview').onclick=()=>post('crash',{do:'view'});
$('a-crashno').onclick=e=>{e.preventDefault();post('crash',{do:'dismiss'});$('crash').hidden=true};
document.addEventListener('click',e=>{const a=e.target.closest('#a-issues,a.issues');if(!a)return;e.preventDefault();post('crash',{do:'issues'})});
$('b-quit').onclick=()=>{const g=(S&&S.games||[]).length;
  if(g&&!confirm('A game is running through H2Link. Closing it cuts that game off from the others. Close anyway?'))return;
  closed=true;post('quit');setTimeout(()=>{try{window.close()}catch(e){}},400)};
let planHold=0;
const sendPlan=()=>{planHold=Date.now()+1500;post('roomset',{level:$('f-level').value,difficulty:$('f-diff').value,tick:$('f-tick').value,
  cheats:$('f-cheats').checked,skulls:[...document.querySelectorAll('#skulls input:checked')].map(i=>i.dataset.skull)})};
$('plan').addEventListener('change',sendPlan);
$('b-report').onclick=()=>post('report');
$('b-copy').onclick=()=>{const t=S.share,done=()=>{$('b-copy').textContent='Copied';setTimeout(()=>$('b-copy').textContent='Copy address',1500)};
  if(navigator.clipboard)navigator.clipboard.writeText(t).then(done);
  else{const a=document.createElement('textarea');a.value=t;document.body.appendChild(a);a.select();document.execCommand('copy');a.remove();done()}};
$('f-addr').addEventListener('keydown',e=>{if(e.key==='Enter')$('b-join').click()});
$('b-chat').onclick=sendChat;$('f-chat').addEventListener('keydown',e=>{if(e.key==='Enter')sendChat()});
tick();setInterval(tick,1000);
</script></body></html>
"""


def make_handler(engine, token):
    page = PAGE_HTML.replace("__TOKEN__", token).encode()

    class Handler(BaseHTTPRequestHandler):
        server_version = APP

        def log_message(self, *a):
            pass

        def _send(self, code, ctype, body):
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def _local(self):
            host = (self.headers.get("Host") or "").split(":")[0]
            return host in ("127.0.0.1", "localhost")

        def do_GET(self):
            if not self._local():
                return self._send(403, "text/plain", b"forbidden")
            if self.path == "/":
                self._send(200, "text/html; charset=utf-8", page)
            elif self.path == "/favicon.ico":
                self._send(200, "image/x-icon", ICON_ICO)
            elif self.path.startswith("/api/state"):
                engine.page_seen = now()
                self._send(200, "application/json", json.dumps(engine.snap).encode())
            elif self.path.startswith("/api/rooms"):
                q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
                text = (q.get("server") or [""])[0].strip()
                if text == "@builtin":
                    text = engine.cfg.get("server", "")
                out = query_rooms(text) if text else dict(ok=False, error="")
                self._send(200, "application/json", json.dumps(out).encode())
            else:
                self._send(404, "text/plain", b"not found")

        def do_POST(self):
            # The token keeps other web pages in the browser from driving the tunnel.
            if not self._local() or self.headers.get("X-H2Link") != token:
                return self._send(403, "text/plain", b"forbidden")
            cmd = self.path.rsplit("/", 1)[-1]
            try:
                n = min(int(self.headers.get("Content-Length") or 0), 65536)
                body = json.loads(self.rfile.read(n) or b"{}")
            except ValueError:
                body = {}
            if cmd == "quit":
                engine.command("quit")
                self._send(200, "application/json", b"{}")
            elif cmd == "show":                     # a second start of H2Link: bring this window up
                if SHOW_WINDOW[0]:
                    try:
                        SHOW_WINDOW[0]()
                    except Exception:
                        pass
                self._send(200, "application/json", json.dumps(dict(shown=bool(SHOW_WINDOW[0]))).encode())
            elif cmd in ("host", "join", "leave", "launch", "settings", "report", "roomset", "chat", "update", "crash") and isinstance(body, dict):
                engine.command(cmd, body)
                time.sleep(0.15)
                self._send(200, "application/json", b"{}")
            else:
                self._send(404, "text/plain", b"not found")

    return Handler


def load_cfg(path):
    cfg = {}
    try:
        with open(path) as f:
            cfg = json.load(f)
    except (OSError, ValueError):
        pass
    cfg.setdefault("name", os.environ.get("USERNAME") or os.environ.get("USER") or "Player")
    if not cfg.get("game_dir") or not os.path.isdir(cfg["game_dir"]):
        here = os.path.dirname(os.path.abspath(path))
        cfg["game_dir"] = next((d for d in (here, os.path.dirname(here)) if glob.glob(os.path.join(d, "halo2*.exe"))), "")
    shipped = ""
    for fname in ("server.key", "server.txt"):      # put there by whoever hands out the folder
        try:
            with open(os.path.join(os.path.dirname(os.path.abspath(path)), fname), encoding="utf-8-sig", errors="replace") as f:
                lines = [ln.strip() for ln in f if ln.strip() and not ln.lstrip().startswith("#")]
        except OSError:
            continue
        if lines:
            shipped = lines[0]
            break
    # The file wins when it is new or was edited; otherwise what the player last used stays.
    if shipped and (not cfg.get("server") or shipped != cfg.get("server_file")):
        cfg["server"] = shipped
    cfg["server_file"] = shipped
    cfg.setdefault("server", "")
    cfg.setdefault("port", DEFAULT_PORT)
    cfg.setdefault("want", 1)
    mark = machine_mark()
    if cfg.get("machine") not in (None, mark):
        # This settings file was made on another PC. Its identity must not come along, or the server
        # takes both PCs for one and they push each other out of the room.
        for k in ("uuid", "name", "init_hash"):
            cfg.pop(k, None)
        cfg["name"] = os.environ.get("USERNAME") or os.environ.get("USER") or "Player"
    cfg["machine"] = mark
    cfg.setdefault("uuid", os.urandom(16).hex())
    return cfg


def console_for_commands():
    """H2Link.exe is built as a window program, so it never opens a console window. When it is started from a
    Command Prompt (the lobby server, --make-key ...), its output goes to that Command Prompt instead."""
    if not IS_WIN or sys.stdout is not None:
        return
    try:
        if ctypes.windll.kernel32.AttachConsole(-1):        # ATTACH_PARENT_PROCESS
            sys.stdout = open("CONOUT$", "w", encoding="utf-8", errors="replace", buffering=1)
            sys.stderr = sys.stdout
    except Exception:
        pass

def main():
    console_for_commands()
    ap = argparse.ArgumentParser(description="%s %s - system link tunnel for the Halo 2 Tag Test sysnet builds" % (APP, VERSION))
    ap.add_argument("--config", help="settings file (default: h2link.json next to this script)")
    ap.add_argument("--host", action="store_true", help="open a room right away")
    ap.add_argument("--join", metavar="ADDRESS", help="join the room at ADDRESS[:PORT] right away")
    ap.add_argument("--room", metavar="NAME", help="with --join: ADDRESS is a lobby server, enter this room on it")
    ap.add_argument("--make-key", metavar="ADDRESS",
                    help="print a server key for ADDRESS[:PORT]; put it in server.key so the address is not readable")
    ap.add_argument("--key-out", metavar="FILE",
                    help="with --make-key: write the key to FILE (as server.key) instead of only printing it")
    ap.add_argument("--relay-only", action="store_true",
                    help="with --server: never tell PCs each other's addresses; all traffic goes through the server")
    ap.add_argument("--server", action="store_true",
                    help="run as a lobby server (no game, no control page): python h2link.py --server --port %d" % DEFAULT_PORT)
    ap.add_argument("--name")
    ap.add_argument("--port", type=int, help="UDP port of this PC (default %d)" % DEFAULT_PORT)
    ap.add_argument("--password")
    ap.add_argument("--game-dir")
    ap.add_argument("--slots", type=int, help="game windows on this PC, 1 to %d (default 1)" % MAX_WINDOWS)
    ap.add_argument("--ui-port", type=int, default=UI_PORT)
    ap.add_argument("--no-ui", action="store_true", help="no web page, log to the console only")
    ap.add_argument("--no-browser", action="store_true", help="do not open the web page automatically")
    ap.add_argument("--stay", action="store_true", help="keep running with no page open (default: close after 3 idle minutes)")
    ap.add_argument("--second", action="store_true", help="start even though an H2Link is already running on this PC")
    # test hooks: several "PCs" on one machine, bad links
    for flag in ("--loop-ip", "--page-file", "--wan-bind"):
        ap.add_argument(flag, help=argparse.SUPPRESS)
    ap.add_argument("--sim-loss", type=float, default=0.0, help=argparse.SUPPRESS)
    ap.add_argument("--sim-delay", type=float, default=0.0, help=argparse.SUPPRESS)
    ap.add_argument("--no-direct", action="store_true", help=argparse.SUPPRESS)
    ap.add_argument("--install-game", metavar="GAME_FOLDER",
                    help="make H2Link's game files in the H2EK folder from its own originals (backing them up), then exit")
    ap.add_argument("--check-game", metavar="GAME_FOLDER",
                    help="check that every H2EK original H2Link's game files are made from is there, then exit")
    ap.add_argument("--log", metavar="FILE",
                    help="with --install-game, --check-game or --restore-game: also write what happens to FILE")
    ap.add_argument("--restore-game", metavar="GAME_FOLDER",
                    help="put the H2EK originals back and remove H2Link's game files, then exit")
    opts = ap.parse_args()
    if opts.install_game or opts.check_game or opts.restore_game:
        logf = None
        if opts.log:
            try:
                logf = open(opts.log, "w", encoding="utf-8")
            except OSError:
                pass
        def say(text):
            print(text)
            if logf:
                logf.write(text + "\n")
                logf.flush()
        if opts.install_game:
            say("H2Link %s: game files in %s" % (VERSION, opts.install_game))
            return install_game(opts.install_game, say=say)
        if opts.check_game:
            return install_game(opts.check_game, say=say, check_only=True)
        say("H2Link %s: restoring %s" % (VERSION, opts.restore_game))
        return restore_game(opts.restore_game, say=say)

    if opts.make_key:
        try:
            host, port = split_addr(opts.make_key)
            if not host or " " in host or "/" in host:
                raise ValueError
            key = make_server_key(opts.make_key)
        except ValueError:
            print("Not an address: %s\nUse an IP or a host name, with :PORT only if the server is not on %d."
                  % (opts.make_key, DEFAULT_PORT))
            return 1
        print(key)
        if opts.key_out:
            try:
                with open(opts.key_out, "w", encoding="utf-8") as f:
                    f.write("# Lobby server chosen when H2Link was installed: %s, UDP port %d\n%s\n" % (host, port, key))
            except OSError as e:
                print("Could not write %s: %s" % (opts.key_out, e))
                return 1
        print("\nThis key leads to %s, UDP port %d." % (host, port))
        try:
            ip = socket.gethostbyname(host)
            if private_ip(ip):
                print("Note: %s is an address inside a home or office network. The key works for PCs on that "
                      "network only; players elsewhere need a key made from the public address." % ip)
        except OSError:
            print("WARNING: the name \"%s\" cannot be looked up from this machine. Players will be told the key "
                  "does not work. Check the spelling, or use the IP address." % host)
        return 0
    if opts.server:
        log = Log(echo=True)
        try:
            srv = Server(opts.wan_bind, opts.port or DEFAULT_PORT, log, opts.relay_only)
        except OSError as e:
            log.error("UDP port %d cannot be opened (%s)" % (opts.port or DEFAULT_PORT, e))
            return 1
        log.info("%s %s lobby server on UDP port %d%s" % (APP, VERSION, opts.port or DEFAULT_PORT,
                 ", relay only: PCs are not told each other's addresses" if opts.relay_only else ""))
        try:
            import signal
            signal.signal(signal.SIGTERM, lambda *_: setattr(srv, "stop", True))
        except (ImportError, ValueError, OSError):
            pass
        try:
            srv.run()
        except KeyboardInterrupt:
            pass
        log.info("Server stopped")
        log.flush()
        return 0

    # One H2Link per PC. A second start (the window was left open, or the file was double-clicked
    # again) only brings the running one's page up.
    if not (opts.no_ui or opts.second or opts.config):
        url = running_instance(opts.ui_port)
        if url:
            print("H2Link is already running on this PC. Its page: %s" % url)
            print("This window closes by itself.")
            if not opts.no_browser and not show_running(url):
                try:
                    open_page(url)
                except Exception:
                    pass
            time.sleep(4)
            return 0

    here = os.path.dirname(os.path.abspath(sys.argv[0]))
    cfg_path = opts.config or os.path.join(here, "h2link.json")
    cfg = load_cfg(cfg_path)
    for key, val in (("name", opts.name), ("port", opts.port), ("password", opts.password),
                     ("game_dir", opts.game_dir), ("want", opts.slots)):
        if val is not None:
            cfg[key] = val
    try:                                # saved before the limit, or given on the command line
        cfg["want"] = min(MAX_WINDOWS, max(1, int(cfg.get("want", 1))))
    except (TypeError, ValueError):
        cfg["want"] = 1
    log = Log(echo=True)
    log.info("%s %s" % (APP, VERSION))
    eng = Engine(cfg, cfg_path, log, opts)
    threading.Thread(target=eng.game_files_check, daemon=True).start()
    threading.Thread(target=eng.clean_game_logs, daemon=True).start()
    eng.save_cfg()
    if not eng.plat.atomic.ok:
        log.warn("Atomic page writes are not available on this Python build; using plain writes")
    eng.start()
    if opts.host:
        eng.command("host", {})
    elif opts.join and opts.room:
        eng.command("join", {"server": opts.join, "room": opts.room, "via": "server"})
    elif opts.join:
        eng.command("join", {"address": opts.join})

    httpd = None
    gui = None
    if not opts.no_ui:
        token = os.urandom(12).hex()
        for port in range(opts.ui_port, opts.ui_port + 10):
            try:
                httpd = ThreadingHTTPServer(("127.0.0.1", port), make_handler(eng, token))
                break
            except OSError:
                continue
        if httpd:
            url = "http://127.0.0.1:%d/" % httpd.server_address[1]
            threading.Thread(target=httpd.serve_forever, daemon=True).start()
            log.info("Control page: %s" % url)
            if not opts.no_browser:
                hide_console()                      # the window takes over (H2Link.exe only)
                try:
                    import webview as gui           # H2Link.exe: its own window (pywebview, WebView2)
                except Exception:
                    gui = None
                if gui is None:
                    try:
                        open_page(url)
                    except Exception:
                        pass
        else:
            log.warn("Could not open the control page port; running without it")
    try:
        import signal
        signal.signal(signal.SIGTERM, lambda *_: eng.command("quit"))
    except (ImportError, ValueError, OSError):
        pass
    # With its page closed and nothing depending on it, H2Link closes itself: a forgotten window would
    # keep holding the game's slots and this PC's place in the room.
    watch = bool(httpd) and not opts.no_browser and not opts.stay
    eng.page_seen = now()
    if gui is not None:
        try:
            rc = run_window(gui, url, eng, log, httpd)
            if rc is not None:
                return rc
        except Exception as e:                       # no WebView2 on this PC: the app window instead
            log.warn("H2Link's own window could not open (%s) - using the browser" % e)
        SHOW_WINDOW[0] = None
        open_page(url)                               # (also when the window stayed empty: see run_window)
    title = None
    try:
        while eng.is_alive():
            time.sleep(0.5)
            snap = eng.snap or {}
            in_room, games = snap.get("mode") in ("host", "client"), snap.get("games") or []
            needed = bool(games) or (snap.get("mode") == "host" and snap.get("players", 0) > 1)
            text = "H2Link - " + ("in %s" % snap.get("room") if in_room else "not in a room") + \
                   (", game running" if games else "")
            if text != title:
                title = text
                console_title(text)
            if needed:
                eng.page_seen = now()               # a game is running through it, or others play in its room
            elif watch and now() - eng.page_seen > IDLE_EXIT:
                log.info("No H2Link page has been open for %d minutes and no game is running - closing"
                         % (IDLE_EXIT // 60))
                break
    except KeyboardInterrupt:
        pass
    eng.command("quit")
    eng.join(3)
    close_page_window()
    log.flush()
    if httpd:
        httpd.shutdown()


def run_window(gui, url, eng, log, httpd):
    """H2Link.exe's own window (pywebview on WebView2). It runs on the main thread; closing it closes H2Link
    (after asking, if a game is running through it). The page's Close H2Link button closes the window too."""
    # tall enough for a room page without scrolling (about 1000 px) where the screen allows; smaller screens
    # get a window that fits them, and the page scrolls
    w, h = 1280, 1000
    try:
        sc = gui.screens[0]
        w, h = min(w, sc.width - 40), min(h, sc.height - 60)
    except Exception:
        pass
    win = gui.create_window("H2Link", url, width=w, height=h, min_size=(980, 640),
                            background_color="#0a1a33", text_select=True)
    def show():
        win.restore()
        win.show()
    SHOW_WINDOW[0] = show
    def closing():
        games = (eng.snap or {}).get("games") or []
        if games and eng.is_alive():
            return win.create_confirmation_dialog(
                "H2Link", "A game is running through H2Link. Closing H2Link cuts that game off from the others. "
                "Close anyway?")
        return True
    try:
        win.events.closing += closing
    except Exception:
        pass
    def follow():                                    # the page's Close button stopped the engine: window too
        while eng.is_alive():
            time.sleep(0.5)
        try:
            win.destroy()
        except Exception:
            pass
    threading.Thread(target=follow, daemon=True).start()
    # The page asks H2Link for its state every second. If the window has not asked within 12 s, its web view
    # cannot show the page (an old or broken WebView2): the window closes and the page opens in Edge instead.
    empty = [False]
    seen0 = eng.page_seen
    def watchdog():
        time.sleep(12)
        if eng.is_alive() and eng.page_seen <= seen0:
            empty[0] = True
            log.warn("H2Link's window stayed empty - opening its page in Edge instead")
            try:
                win.destroy()
            except Exception:
                pass
    threading.Thread(target=watchdog, daemon=True).start()
    # pywebview reports a missing or damaged WebView2 runtime only in its log: watch for it.
    try:
        import logging

        class NoWebView2(logging.Handler):
            """WebView2 could not start (missing or damaged runtime): the page goes to Edge at once."""
            def emit(self, rec):
                if empty[0] or "WebView2 initialization failed" not in rec.getMessage():
                    return
                empty[0] = True
                log.warn("Microsoft's WebView2 runtime is missing or damaged on this PC, so H2Link's own window "
                         "cannot show its page - opening it in Edge instead. To fix it: Settings > Apps > "
                         "Microsoft Edge WebView2 Runtime > Modify > Repair (or install the WebView2 Runtime "
                         "from Microsoft).")
                threading.Thread(target=lambda: (time.sleep(0.2), win.destroy()), daemon=True).start()
        lg = logging.getLogger("pywebview")
        lg.addHandler(NoWebView2())
        lg.setLevel(logging.ERROR)
    except Exception:
        pass
    def started():
        r = getattr(gui, "renderer", "?")
        if r not in ("edgechromium", "?"):              # not WebView2: it cannot show the page
            empty[0] = True
            log.warn("H2Link's window got the %s engine, not WebView2 - opening its page in Edge instead" % r)
            win.destroy()
    try:
        gui.start(started, gui="edgechromium")       # WebView2 only: never the old Internet Explorer engine
    except TypeError:
        gui.start()
    if empty[0]:
        return None                                  # main() goes on with the page in Edge
    # until the window closes
    SHOW_WINDOW[0] = None
    eng.command("quit")
    eng.join(3)
    log.flush()
    if httpd:
        httpd.shutdown()
    return 0


if __name__ == "__main__":
    sys.exit(main())
