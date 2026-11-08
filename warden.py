import math
import os
import queue
import random
import re
import threading
import time

import minescript
from java import JavaClass

try:
    import winsound
except Exception:
    winsound = None

# ── SETTINGS ──────────────────────────────────────────────────────────────────
# Auto-click
CLICK_MIN          = 0.8
CLICK_MAX          = 0.9
CLICK_HOLD         = 0.1
MOVE_ALARM_BLOCKS  = 4.0     # alarm if you end up this many blocks from your original position
RESUME_DELAY       = 1.0
LEFT_CLICK_ENABLES = True    # a real left click turns auto-click back on

# Alarms
ALARM_ACTION       = "beep"         # "beep" = winsound alarm (P to silence), "disconnect" = leave the server
MOVE_ALARM         = True    # moved MOVE_ALARM_BLOCKS from the original position -> alarm (also stops clicking)
MSG_ALARM          = True    # someone sends you a /msg -> alarm
PLAYER_ALARM       = True    # another player comes within PLAYER_RANGE -> alarm
PLAYER_RANGE       = 20      # blocks
PLAYER_CHECK       = 0.5     # how often to look for players (seconds)
HOTBAR_ALARM       = True    # hotbar items added / removed / moved / count changed -> alarm
HOTBAR_IGNORE_ADDED = ["armadillo_scute"]   # these may be ADDED without an alarm
                                            # (moving or removing them still alarms)
HOTBAR_CHECK       = 0.25    # how often to compare the hotbar (seconds)
PLAYER_WHITELIST   = ["Westl1fe", "LexQiqi", "Ivaniam", "Svea", "014K","MunggoFriday0926","Kashg"]   # case-insensitive

# Target check
ONLY_WARDEN        = True    # only click while a warden is under the crosshair
TARGET_RANGE       = 6       # how far to look for the target (blocks)

# Aim assist (smooth look + jitter, warden in front of you only)
AIM                = True
AIM_RANGE          = 12      # only wardens within this many blocks
AIM_FOV            = 45      # only wardens within +/- this many degrees of where you
                             # are already looking (so nothing behind/beside you)
AIM_SCAN           = 0.1     # how often to search for wardens (seconds)
AIM_TURN_SPEED     = 110     # degrees per second when turning toward the warden
AIM_MIN_TIME       = 0.15    # shortest smooth_look (seconds)
AIM_MAX_TIME       = 0.80    # longest smooth_look (seconds)
AIM_RETRACK        = 2.5     # re-aim straight away if the crosshair is off by more than this (degrees)
AIM_JITTER         = 0.8     # crosshair wobble left/right (degrees)
AIM_JITTER_TIME    = 0.40    # how long each little wobble move takes (seconds)
AIM_JITTER_MIN     = 1.0     # seconds between wobble moves (random between min and max)
AIM_JITTER_MAX     = 3.0
AIM_PITCH          = 0.0     # pitch is locked to this (0 = straight ahead, never up).
                             # Set to None to never touch pitch at all.
AIM_PITCH_JITTER   = 0.25    # extra DOWNWARD wobble only (degrees), never up. 0 = off

# Strafe (left 1s, right 1s)
STRAFE             = True
STRAFE_EVERY       = 20      # seconds between strafes
STRAFE_TIME        = 1.0     # seconds each direction
STRAFE_SETTLE      = 0.6     # seconds after strafing where the move alarm stays quiet

# Sword
AUTO_SWORD         = True
SWORD_KEYWORD      = "sword"
SWORD_PRIORITY     = ["netherite", "diamond", "iron", "stone", "golden", "wooden"]
SWORD_CHECK        = 0.5

# Auto-feed
AUTO_FEED          = True
FEED_COMMAND       = "/feed"
FEED_EVERY         = 300
FEED_ON_START      = False

# Anti-AFK (fast)
AFK_PHRASES       = ["afk check"]
AFK_HOLD_SECONDS  = 10
AFK_OPEN_WAIT     = 0.25
AFK_CLICK_MIN     = 0.10
AFK_CLICK_MAX     = 0.25
AFK_GUI_TIMEOUT   = 55

GUI_WAIT          = 4.0

# Alarm sound
BEEP_FREQ = 1000
BEEP_MS   = 400

START_PAUSED = False
AUTO_CLICK   = True
DEBUG        = False
STATUS       = True     # print why it isn't clicking (once per change)
TAG = "[AutoClick]"

# GLFW key codes
CLICK_KEY  = 295   # F6
TOGGLE_KEY = 296   # F7
FEED_KEY   = 297   # F8
STOP_KEY   = 298   # F9 stop the script
ALARM_OFF_KEY = 80 # P  silence the alarm

# ── Java classes ──────────────────────────────────────────────────────────────
Minecraft = JavaClass("net.minecraft.client.Minecraft")

def first_class(*names):
    for n in names:
        try:
            return JavaClass(n)
        except Exception:
            pass
    return None

ClickEnum = first_class(
    "net.minecraft.world.inventory.ContainerInput",
    "net.minecraft.world.inventory.ClickType",
)

CLICK_METHODS = ("handleContainerInput", "handleInventoryMouseClick")
click_method = None          # remembered after the first successful click

# ── State ─────────────────────────────────────────────────────────────────────
stopped = False
paused = START_PAUSED
alarm_on = False
disconnecting = False
auto_click_on = AUTO_CLICK
auto_feed_on = AUTO_FEED

next_feed_t = 0.0

last_sword_check = 0.0
sword_ok = False
last_sword_warn = 0.0

ac_next_t = 0.0
ac_release_t = 0.0
ac_base = None
origin_pos = None            # the "original position" the move alarm measures from
ac_was_blocked = True

afk_active = False
afk_open_t = 0.0
afk_hold_until = 0.0
afk_next_click_t = 0.0
afk_clicked = set()

last_chat_norm = ""
last_chat_t = 0.0
warned = set()

last_status = ""
last_status_t = 0.0

last_player_check = 0.0
last_hotbar_check = 0.0
hotbar_base = None           # snapshot of the hotbar to compare against
players_alerted = set()      # players already alarmed for (cleared when they leave range)
WL = set(n.lower() for n in PLAYER_WHITELIST)

# strafe state
strafe_state = "idle"        # idle, left, right
strafe_until = 0.0
next_strafe_t = 0.0
strafe_settle_until = 0.0

# aim state
aim_pos = None               # (x, z) of the warden we are following
aim_next_scan = 0.0
aim_next_move_t = 0.0
look_cancel = threading.Event()
look_thread = None

# ── Helpers ───────────────────────────────────────────────────────────────────
def say(text):
    minescript.echo(TAG + " " + text)

def dbg(text):
    if DEBUG:
        say("(dbg) " + text)

def warn_once(key, text):
    if key not in warned:
        warned.add(key)
        say(text)

def status(reason):
    # print the reason only when it changes (or every 15 s)
    global last_status, last_status_t
    if not STATUS:
        return
    now = time.time()
    if reason != last_status or now - last_status_t > 15:
        last_status = reason
        last_status_t = now
        say("status: " + reason)

def norm(s):
    s = str(s).lower()
    s = re.sub(r"\u00a7.", "", s)
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return " ".join(s.split())

NAFK = [norm(p) for p in AFK_PHRASES]

# incoming private message, e.g. "MSG (SomeName ➜ me)"; your own "(me ➜ Name)" doesn't match
MSG_RE = re.compile("MSG \\((.+?)\\s*➜\\s*me\\)", re.I)

def press_attack(state):
    try:
        minescript.player_press_attack(state)
    except Exception:
        try:
            minescript.press_key_bind("key.attack", state)
        except Exception as e:
            say("left-click failed: " + str(e))

def release_attack():
    global ac_release_t
    ac_release_t = 0.0
    press_attack(False)

def gui_is_open():
    s = minescript.screen_name()
    return s is not None and "chat" not in str(s).lower()

def wrap180(a):
    return (a + 180.0) % 360.0 - 180.0

def clamp(v, lo, hi):
    return max(lo, min(hi, v))

# ── Chat via latest.log ───────────────────────────────────────────────────────
try:
    _here = os.path.dirname(os.path.abspath(__file__))
except Exception:
    _here = os.getcwd()
LOG_PATH = os.path.normpath(os.path.join(_here, "..", "logs", "latest.log"))
log_file = None
log_buf = b""

def log_open():
    global log_file
    try:
        log_file = open(LOG_PATH, "rb")
        log_file.seek(0, 2)
    except Exception as e:
        log_file = None
        say("Can't read " + LOG_PATH + ": " + str(e))

def log_tick():
    global log_file, log_buf
    if log_file is None:
        return
    try:
        if os.path.getsize(LOG_PATH) < log_file.tell():
            log_file.seek(0)
            log_buf = b""
        data = log_file.read()
    except Exception:
        return
    if not data:
        return
    log_buf += data
    parts = log_buf.split(b"\n")
    log_buf = parts[-1]
    for raw in parts[:-1]:
        text = raw.decode("utf-8", "replace")
        i = text.find("[CHAT] ")
        if i >= 0:
            on_chat(text[i + 7:].strip())

# ── Alarm / disconnect ────────────────────────────────────────────────────────
def alarm_loop():
    while alarm_on and not stopped:
        try:
            if winsound is not None:
                winsound.Beep(BEEP_FREQ, BEEP_MS)
            else:
                time.sleep(BEEP_MS / 1000.0)
        except Exception:
            time.sleep(BEEP_MS / 1000.0)
        time.sleep(0.3)

def disconnect_now(reason):
    global disconnecting, stopped
    mc = Minecraft.getInstance()
    errs = []
    msg = None
    try:
        msg = JavaClass("net.minecraft.network.chat.Component").literal(TAG + " " + reason)
    except Exception as e:
        errs.append("component: " + str(e)[:60])
    attempts = (
        lambda: mc.getConnection().getConnection().disconnect(msg),
        lambda: mc.level.disconnect(msg),
    )
    for fn in attempts:
        try:
            fn()
            disconnecting = True
            stopped = True
            return True
        except Exception as e:
            errs.append(str(e)[:60])
    say("disconnect failed: " + " | ".join(errs))
    return False

def trigger_alarm(reason, allow_disconnect=True):
    global alarm_on
    if alarm_on or disconnecting:
        return
    release_attack()
    strafe_stop()
    if ALARM_ACTION == "disconnect" and allow_disconnect:
        say("ALARM: " + reason + " -> disconnecting")
        if disconnect_now(reason):
            return
        say("Disconnect failed, using the beep alarm instead")
    alarm_on = True
    if winsound is None:
        say("winsound isn't available (Windows only) - no sound will play")
    try:
        minescript.echo_json({
            "text": TAG + " ALARM: " + reason + "  (press P to silence)",
            "color": "red"})
    except Exception:
        say("ALARM: " + reason + "  (press P to silence)")
    threading.Thread(target=alarm_loop, daemon=True).start()

# ── GUI clicking (used by the AFK check) ──────────────────────────────────────
def click_many(slots, mode_name="PICKUP"):
    # Click each slot in `slots` once, in order. Looks up the Java objects ONCE
    # and remembers which click method works.
    # Returns how many clicks were sent.
    global click_method
    if not slots:
        return 0
    mc = Minecraft.getInstance()
    player = mc.player
    cid = player.containerMenu.containerId
    gm = mc.gameMode
    try:
        mode = getattr(ClickEnum, mode_name)
    except Exception as e:
        say("click mode " + mode_name + " unavailable: " + str(e))
        return 0

    fn = getattr(gm, click_method) if click_method else None
    done = 0
    last = None
    for slot in slots:
        if fn is None:
            for m in CLICK_METHODS:
                try:
                    getattr(gm, m)(cid, slot, 0, mode, player)
                    click_method = m
                    fn = getattr(gm, m)
                    done += 1
                    break
                except Exception as e:
                    last = e
            else:
                say("click failed: " + str(last))
                break
            continue
        try:
            fn(cid, slot, 0, mode, player)
            done += 1
        except Exception as e:
            say("click failed: " + str(e))
            break
    return done

def click_slot(slot, mode_name="PICKUP"):
    return click_many([slot], mode_name) == 1

# ── Anti-AFK ──────────────────────────────────────────────────────────────────
def find_targets():
    out = []
    try:
        items = minescript.container_get_items()
    except Exception:
        return out
    if not items:
        return out
    for i in items:
        if i.nbt and "Click me" in i.nbt:
            out.append(i.slot)
    return out

def afk_tick(t):
    global afk_active, afk_open_t, afk_next_click_t, afk_hold_until
    if alarm_on:
        return
    gui = gui_is_open()

    if not afk_active:
        if not gui:
            return
        targets = find_targets()
        if not targets:
            return
        afk_active = True
        afk_open_t = t
        afk_next_click_t = t + AFK_OPEN_WAIT + random.uniform(0, 0.1)
        afk_clicked.clear()
        release_attack()
        say("AFK check detected: " + str(len(targets)) + " target(s), auto-click paused")
        return

    if not gui:
        afk_active = False
        afk_hold_until = 0.0
        afk_clicked.clear()
        say("AFK check done, auto-click resumes")
        return

    if t - afk_open_t > AFK_GUI_TIMEOUT:
        trigger_alarm("AFK GUI still open after " + str(AFK_GUI_TIMEOUT) + "s")
        return

    if t < afk_next_click_t:
        return

    for slot in find_targets():
        if slot in afk_clicked:
            continue
        if click_slot(slot):
            afk_clicked.add(slot)
            say("Clicked slot " + str(slot))
            afk_next_click_t = t + random.uniform(AFK_CLICK_MIN, AFK_CLICK_MAX)
        else:
            trigger_alarm("Could not click the AFK item (click method failed)")
        return

# ── Sword ─────────────────────────────────────────────────────────────────────
def holding_sword():
    try:
        mh = minescript.player_hand_items().main_hand
        return mh is not None and SWORD_KEYWORD in str(mh.item).lower()
    except Exception:
        return True

def find_sword_slot():
    try:
        inv = minescript.player_inventory()
    except Exception:
        return None
    best_slot = None
    best_rank = None
    for it in inv:
        if it.slot is None or not (0 <= it.slot <= 8):
            continue
        name = str(it.item).lower()
        if SWORD_KEYWORD not in name:
            continue
        rank = len(SWORD_PRIORITY)
        for i, tier in enumerate(SWORD_PRIORITY):
            if tier in name:
                rank = i
                break
        if best_rank is None or rank < best_rank:
            best_rank = rank
            best_slot = it.slot
    return best_slot

def ensure_sword(t):
    global last_sword_check, sword_ok, last_sword_warn, ac_was_blocked
    if not AUTO_SWORD:
        return True
    if t - last_sword_check < SWORD_CHECK:
        return sword_ok
    last_sword_check = t

    if holding_sword():
        sword_ok = True
        return True

    sword_ok = False
    slot = find_sword_slot()
    if slot is None:
        if t - last_sword_warn > 10:
            say("No sword in the hotbar - not clicking")
            last_sword_warn = t
        return False
    try:
        minescript.player_inventory_select_slot(slot)
        say("Switched to sword (slot " + str(slot) + ")")
        ac_was_blocked = True
    except Exception as e:
        say("Can't select sword slot: " + str(e))
    return False

# ── Target check (warden under the crosshair) ────────────────────────────────
def _is_warden(text):
    text = str(text).lower()
    return "warden" in text and "armor" not in text    # never an armor stand

def target_seen():
    # Returns (is_warden, description). Checks two independent ways.
    desc = []

    # 1) Minescript's own raycast
    try:
        ent = minescript.player_get_targeted_entity(TARGET_RANGE)
        if ent is None:
            desc.append("minescript=none")
        else:
            info = str(ent.type) + " " + str(ent.name)
            desc.append("minescript=" + info)
            if _is_warden(ent.type):
                return True, " | ".join(desc)
    except Exception as e:
        desc.append("minescript=err(" + str(e)[:40] + ")")

    # 2) the game's own crosshair entity
    try:
        ent = Minecraft.getInstance().crosshairPickEntity
        if ent is None:
            desc.append("game=none")
        else:
            info = str(ent.getType())
            desc.append("game=" + info)
            if _is_warden(info):
                return True, " | ".join(desc)
    except Exception as e:
        desc.append("game=err(" + str(e)[:40] + ")")

    return False, " | ".join(desc)

def looking_at_warden():
    if not ONLY_WARDEN:
        return True
    ok, desc = target_seen()
    if not ok:
        status("not looking at a warden (" + desc + ")")
    return ok

# ── Blocking conditions ───────────────────────────────────────────────────────
def blocked_reason(t):
    # None = free to run, otherwise a text reason (quiet; doesn't print)
    if alarm_on:
        return "alarm is on (P to silence)"
    if paused:
        return "paused (F7 to resume)"
    if afk_active:
        return "AFK check in progress"
    if t < afk_hold_until:
        return "AFK check announced, waiting"
    s = minescript.screen_name()
    if s is not None:
        return "a screen is open: " + str(s)
    return None

def autoclick_blocked(t):
    r = blocked_reason(t)
    if r is not None:
        status(r)
        return True
    return False

# ── Smooth aim (smooth_look, yaw only, warden in front of you only) ──────────
def _fallback_look(yaw, pitch, duration):
    # own smoothstep look, used if minescript.smooth_look isn't usable
    try:
        y0, p0 = minescript.player_orientation()
    except Exception:
        minescript.player_set_orientation(yaw, pitch)
        return
    steps = max(1, int(duration / 0.02))
    for i in range(1, steps + 1):
        if look_cancel.is_set() or stopped:
            return
        k = i / steps
        k = k * k * (3 - 2 * k)
        dyaw = wrap180(yaw - y0)
        minescript.player_set_orientation(y0 + dyaw * k, p0 + (pitch - p0) * k)
        time.sleep(0.02)

def do_smooth_look(yaw, pitch, duration):
    sl = getattr(minescript, "smooth_look", None)
    if sl is not None:
        try:
            sl(yaw, pitch, duration)
            return
        except Exception as e:
            warn_once("smooth_look", "smooth_look failed, using built-in fallback: " + str(e))
    _fallback_look(yaw, pitch, duration)

def start_look(yaw, pitch, duration):
    # runs the head movement in a thread so the safety checks never block
    global look_thread
    def run():
        try:
            do_smooth_look(yaw, pitch, duration)
        except Exception as e:
            dbg("look thread error: " + str(e))
    look_thread = threading.Thread(target=run, daemon=True)
    look_thread.start()

def scan_warden(yaw, mypos):
    # nearest-to-crosshair warden inside the front cone, as (x, z) or None
    try:
        lst = minescript.entities(max_distance=AIM_RANGE)
    except Exception:
        try:
            lst = minescript.entities()
        except Exception as e:
            warn_once("entities", "Can't list entities: " + str(e))
            return None
    best = None
    best_diff = None
    for e in lst or []:
        if not _is_warden(e.type):
            continue
        dx = e.position[0] - mypos[0]
        dz = e.position[2] - mypos[2]
        d2 = dx * dx + dz * dz
        if d2 < 0.01 or d2 > AIM_RANGE * AIM_RANGE:
            continue
        want = math.degrees(math.atan2(-dx, dz))
        diff = abs(wrap180(want - yaw))
        if diff > AIM_FOV:
            continue                     # behind / beside you -> ignore
        if best is None or diff < best_diff:
            best = (e.position[0], e.position[2])
            best_diff = diff
    return best

def aim_tick(t):
    global aim_pos, aim_next_scan, aim_next_move_t
    if not AIM or not auto_click_on or blocked_reason(t) is not None:
        aim_pos = None
        look_cancel.set()
        return
    if look_thread is not None and look_thread.is_alive():
        return                           # still in the middle of a smooth look
    look_cancel.clear()
    try:
        yaw, pitch = minescript.player_orientation()
        mypos = minescript.player_position()
    except Exception:
        return

    if t >= aim_next_scan:
        aim_next_scan = t + AIM_SCAN
        aim_pos = scan_warden(yaw, mypos)

    if aim_pos is None:
        return                           # no warden in front: leave the view alone

    dx = aim_pos[0] - mypos[0]
    dz = aim_pos[1] - mypos[2]
    if dx * dx + dz * dz < 0.01:
        return
    base = math.degrees(math.atan2(-dx, dz))
    off_target = abs(wrap180(base - yaw)) > AIM_RETRACK
    if not off_target and t < aim_next_move_t:
        return                           # on target: only wobble every few seconds

    dyaw = wrap180(base + random.uniform(-AIM_JITTER, AIM_JITTER) - yaw)
    if off_target:
        duration = clamp(abs(dyaw) / AIM_TURN_SPEED, AIM_MIN_TIME, AIM_MAX_TIME) * random.uniform(0.9, 1.2)
    else:
        duration = AIM_JITTER_TIME
    if AIM_PITCH is None:
        target_pitch = pitch
    else:
        target_pitch = AIM_PITCH + random.uniform(0.0, AIM_PITCH_JITTER)   # level or slightly down, never up
    aim_next_move_t = t + random.uniform(AIM_JITTER_MIN, AIM_JITTER_MAX)
    start_look(yaw + dyaw, target_pitch, duration)

# ── Strafe (left 1s, right 1s, every 20s) ────────────────────────────────────
def press_move(left, right):
    for name, state in (("player_press_left", left), ("player_press_right", right)):
        try:
            getattr(minescript, name)(state)
        except Exception as e:
            warn_once("strafe_" + name, "Can't press move key (" + name + "): " + str(e))

def strafe_stop():
    global strafe_state
    if strafe_state != "idle":
        strafe_state = "idle"
    press_move(False, False)

def strafe_tick(t):
    global strafe_state, strafe_until, next_strafe_t, strafe_settle_until
    can_run = STRAFE and auto_click_on and blocked_reason(t) is None

    if strafe_state != "idle":
        if not can_run:
            strafe_stop()
            strafe_settle_until = t + STRAFE_SETTLE
            return
        if t < strafe_until:
            return
        if strafe_state == "left":
            press_move(False, True)
            strafe_state = "right"
            strafe_until = t + STRAFE_TIME
        else:
            strafe_stop()
            strafe_settle_until = t + STRAFE_SETTLE
            next_strafe_t = t + STRAFE_EVERY
        return

    if not can_run or t < next_strafe_t:
        return
    press_move(True, False)
    strafe_state = "left"
    strafe_until = t + STRAFE_TIME

# ── Auto-click ────────────────────────────────────────────────────────────────
def autoclick_tick(t):
    global ac_next_t, ac_release_t, ac_base, ac_was_blocked, auto_click_on, origin_pos

    if ac_release_t and t >= ac_release_t:
        release_attack()

    if not auto_click_on:
        status("auto-click is OFF (F6 or left click to turn on)")
        return

    if autoclick_blocked(t):
        if ac_release_t:
            release_attack()
        ac_was_blocked = True
        return

    if not ensure_sword(t):
        status("no sword in hand / switching")
        if ac_release_t:
            release_attack()
        ac_was_blocked = True
        return

    pos = tuple(minescript.player_position())

    if ac_was_blocked or ac_base is None:
        ac_base = pos
        ac_was_blocked = False
        ac_next_t = t + RESUME_DELAY
        status("anchored, starting in " + str(RESUME_DELAY) + "s")
        return

    if origin_pos is None:
        origin_pos = pos
        say("Original position set: " + str([round(c, 1) for c in pos]))

    # a 1s strafe covers about 4 blocks, so the distance check is skipped while strafing
    if strafe_state == "idle" and t >= strafe_settle_until:
        dist = sum((a - b) ** 2 for a, b in zip(pos, origin_pos)) ** 0.5
        if dist >= MOVE_ALARM_BLOCKS:
            release_attack()
            msg = ("Moved " + str(round(dist, 1)) + " blocks from the original position " +
                   str([round(c, 1) for c in origin_pos]))
            say(msg)
            if MOVE_ALARM:
                trigger_alarm(msg)
            else:
                origin_pos = pos
            return

    # only hit while a warden is under the crosshair; just wait (forever) if none is there
    if not looking_at_warden():
        return

    if not ac_release_t and t >= ac_next_t:
        status("clicking")
        press_attack(True)
        ac_release_t = t + CLICK_HOLD
        ac_next_t = t + random.uniform(CLICK_MIN, CLICK_MAX)

# ── Player proximity ──────────────────────────────────────────────────────────
def nearby_players():
    # returns {name: distance} for non-whitelisted players within PLAYER_RANGE
    try:
        me = str(minescript.player_name()).lower()
    except Exception:
        me = ""
    try:
        lst = minescript.players(max_distance=PLAYER_RANGE)
    except Exception:
        lst = minescript.players()
    mypos = minescript.player_position()
    out = {}
    for e in lst or []:
        name = str(e.name)
        low = name.lower()
        if low == me or low in WL:
            continue
        d = sum((a - b) ** 2 for a, b in zip(e.position, mypos)) ** 0.5
        if d <= PLAYER_RANGE:
            out[name] = d
    return out

def player_tick(t):
    global last_player_check
    if not PLAYER_ALARM or paused or not auto_click_on:
        players_alerted.clear()
        return
    if t - last_player_check < PLAYER_CHECK:
        return
    last_player_check = t
    try:
        near = nearby_players()
    except Exception as e:
        warn_once("players", "Can't read nearby players: " + str(e))
        return
    for name in list(players_alerted):
        if name not in near:
            players_alerted.discard(name)        # left range, can alarm again later
    for name, d in near.items():
        if name not in players_alerted:
            players_alerted.add(name)
            trigger_alarm("Player nearby: " + name + " (" + str(round(d, 1)) + " blocks)")

# ── Hotbar change ─────────────────────────────────────────────────────────────
def hotbar_snapshot():
    # {slot: (item, count)} for hotbar slots 0-8 (ignores durability/NBT)
    inv = minescript.player_inventory()
    snap = {}
    for it in inv or []:
        if it.slot is None or not (0 <= it.slot <= 8):
            continue
        snap[it.slot] = (str(it.item), getattr(it, "count", 1))
    return snap

def _ignored_item(name):
    return any(k in name for k in HOTBAR_IGNORE_ADDED)

def hotbar_pure_add(old, new):
    # True if this slot only gained an ignorable item (empty -> item, or stack grew)
    if new is None or not _ignored_item(new[0]):
        return False
    if old is None:
        return True
    return old[0] == new[0] and new[1] > old[1]

def hotbar_tick(t):
    global last_hotbar_check, hotbar_base
    # only watch while running; re-baseline after pause / screens / auto-click off
    if (not HOTBAR_ALARM or paused or not auto_click_on or afk_active
            or minescript.screen_name() is not None):
        hotbar_base = None
        return
    if t - last_hotbar_check < HOTBAR_CHECK:
        return
    last_hotbar_check = t
    try:
        snap = hotbar_snapshot()
    except Exception as e:
        warn_once("hotbar", "Can't read hotbar: " + str(e))
        return
    if hotbar_base is None:
        hotbar_base = snap
        return
    if snap == hotbar_base:
        return
    changes = []
    for slot in range(9):
        old = hotbar_base.get(slot)
        new = snap.get(slot)
        if old != new:
            if hotbar_pure_add(old, new):
                continue                    # e.g. an armadillo scute was picked up
            f = lambda v: "empty" if v is None else str(v[1]) + "x " + v[0].replace("minecraft:", "")
            changes.append("slot " + str(slot + 1) + ": " + f(old) + " -> " + f(new))
    hotbar_base = snap                      # new baseline, so it alarms once per change
    if not changes:
        return                              # only ignorable additions happened
    trigger_alarm("Hotbar changed: " + "; ".join(changes))

# ── Auto-feed ─────────────────────────────────────────────────────────────────
def feed_tick(t):
    global next_feed_t
    if not auto_feed_on:
        return
    if alarm_on or paused or afk_active or t < afk_hold_until:
        return
    if t < next_feed_t:
        return
    try:
        minescript.execute(FEED_COMMAND)
        say("Sent " + FEED_COMMAND)
    except Exception as e:
        say("Can't send " + FEED_COMMAND + ": " + str(e))
    next_feed_t = t + FEED_EVERY

# ── Event handlers ────────────────────────────────────────────────────────────
def on_chat(message):
    global afk_hold_until, last_chat_norm, last_chat_t
    message = str(message)
    if message.startswith(TAG):
        return
    low = norm(message)
    now = time.time()
    if low == last_chat_norm and now - last_chat_t < 1.5:
        return
    last_chat_norm = low
    last_chat_t = now

    if any(p in low for p in NAFK):
        afk_hold_until = time.time() + AFK_HOLD_SECONDS
        release_attack()
        strafe_stop()
        say("AFK check announced, auto-click paused")
        return

    if MSG_ALARM and not paused and auto_click_on:
        m = MSG_RE.search(message)
        if m:
            trigger_alarm("MSG from " + m.group(1).strip())

def on_key(event):
    global stopped, paused, alarm_on, auto_click_on, ac_was_blocked, auto_feed_on, next_feed_t
    global origin_pos
    if event.action != 1:
        return
    if DEBUG:
        say("(dbg) key code " + str(event.key))
    if event.key == STOP_KEY:
        stopped = True
        alarm_on = False
        return
    if event.key == ALARM_OFF_KEY:
        # only when no screen is open, so typing "p" in chat doesn't trigger it
        if alarm_on and minescript.screen_name() is None:
            alarm_on = False
            ac_was_blocked = True
            origin_pos = None            # measure from wherever you are now
            say("Alarm silenced" +
                ("" if auto_click_on else " - auto-click is still OFF (F6 or left click)"))
        return
    if alarm_on and event.key in (TOGGLE_KEY, CLICK_KEY) and minescript.screen_name() is None:
        alarm_on = False                 # pausing / switching off also silences the alarm
    if minescript.screen_name() is not None or alarm_on:
        return
    if event.key == TOGGLE_KEY:
        paused = not paused
        if paused:
            release_attack()
            strafe_stop()
        say("PAUSED" if paused else "RUNNING")
    elif event.key == FEED_KEY:
        auto_feed_on = not auto_feed_on
        if auto_feed_on:
            next_feed_t = time.time() + FEED_EVERY
        say("Auto-feed " + ("ON" if auto_feed_on else "OFF"))
    elif event.key == CLICK_KEY:
        auto_click_on = not auto_click_on
        ac_was_blocked = True
        origin_pos = None
        if not auto_click_on:
            release_attack()
            strafe_stop()
        say("Auto-click " + ("ON" if auto_click_on else "OFF"))

def on_mouse(event):
    global auto_click_on, ac_was_blocked, origin_pos
    if not LEFT_CLICK_ENABLES:
        return
    if event.button != 0 or event.action != 1:   # left button, press only
        return
    if auto_click_on or alarm_on:
        return
    if minescript.screen_name() is not None:     # ignore clicks inside menus/chat
        return
    auto_click_on = True
    origin_pos = None
    ac_was_blocked = True                        # re-anchor to the current position
    say("Auto-click ON (left click)")

# ── Main loop ─────────────────────────────────────────────────────────────────
def main():
    global next_feed_t, next_strafe_t
    say("Loaded. " + ("PAUSED - press F7. " if paused else "") +
        "F6 auto-click, F7 pause, F8 auto-feed, P silence alarm, F9 stop, "
        "left click re-enables. Auto-click " +
        ("ON" if auto_click_on else "OFF") + ", auto-feed " + ("ON" if auto_feed_on else "OFF") +
        " (" + FEED_COMMAND + " every " + str(FEED_EVERY) + "s). Alarm action: " + ALARM_ACTION +
        ". Aim " + ("ON" if AIM else "OFF") +
        ", strafe " + ("every " + str(STRAFE_EVERY) + "s" if STRAFE else "OFF"))
    if ClickEnum is None:
        say("WARNING: click class not found; GUI clicking will fail (alarm will sound).")

    sslot = find_sword_slot()
    say("Check: sword slot " + ("NONE FOUND in hotbar" if sslot is None else str(sslot)))

    next_feed_t = time.time() + (0 if FEED_ON_START else FEED_EVERY)
    next_strafe_t = time.time() + STRAFE_EVERY

    log_open()
    with minescript.EventQueue() as events:
        events.register_chat_listener()
        events.register_key_listener()
        events.register_mouse_listener()
        events.register_world_listener()
        try:
            while not stopped:
                try:
                    ev = events.get(timeout=0.02)
                except queue.Empty:
                    ev = None
                while ev is not None:
                    et = ev.type
                    if et == minescript.EventType.CHAT:
                        on_chat(ev.message)
                    elif et == minescript.EventType.KEY:
                        on_key(ev)
                    elif et == minescript.EventType.MOUSE:
                        on_mouse(ev)
                    elif et == minescript.EventType.WORLD:
                        if not ev.connected and not disconnecting:
                            trigger_alarm("Disconnected from the server", allow_disconnect=False)
                    try:
                        ev = events.get(block=False)
                    except queue.Empty:
                        ev = None
                if stopped:
                    break

                log_tick()
                t = time.time()
                afk_tick(t)
                feed_tick(t)
                player_tick(t)
                hotbar_tick(t)
                strafe_tick(t)
                aim_tick(t)
                autoclick_tick(t)
        finally:
            release_attack()
            strafe_stop()
            say("STOPPED")

main()