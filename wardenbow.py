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
# Bow (hold right click = draw, release = shoot)
DRAW_MIN           = 1.05    # seconds to hold right click (full draw is 1.0s, small margin for lag)
DRAW_MAX           = 1.20
SHOT_GAP_MIN       = 0.10    # pause between releasing and starting the next draw
SHOT_GAP_MAX       = 0.30
MOVE_ALARM_BLOCKS  = 4.0     # alarm if you end up this many blocks from your original position
RESUME_DELAY       = 1.0
LEFT_CLICK_ENABLES = True    # a real left click turns auto-shoot back on

# Alarms
ALARM_ACTION       = "beep"         # "beep" = winsound alarm (P to silence), "disconnect" = leave the server
MOVE_ALARM         = True
# Private-message alarm (matches e.g. "MSG (Ivaniam ➜ me) • hello")
MSG_ALARM            = False
MSG_IGNORE_WHITELIST = False   # True = whitelisted senders don't trigger it

# Teleport-message alarm (server says "YC » You got teleported to ... location")
TPMSG_ALARM = True
TPMSG_RE = re.compile(r"You got teleported to .*location", re.IGNORECASE)

PLAYER_ALARM       = True
PLAYER_RANGE       = 20
PLAYER_CHECK       = 0.5
HOTBAR_ALARM       = True
HOTBAR_IGNORE_ADDED = ["armadillo_scute", "arrow"]   # these may be ADDED without an alarm
HOTBAR_IGNORE_COUNT = ["arrow"]                      # count changes of these never alarm (arrows get used up)
HOTBAR_CHECK       = 0.25
PLAYER_WHITELIST   = ["Westl1fe", "LexQiqi", "Ivaniam", "Svea", "014K","MunggoFriday0926","Kashg"]   # case-insensitive

# Target check
ONLY_WARDEN        = True    # only shoot while a warden is under the crosshair
TARGET_RANGE       = 24      # how far to look for the target (blocks)

# Aim assist (smooth look + jitter, warden in front of you only)
AIM                = True
AIM_RANGE          = 24
AIM_FOV            = 45
AIM_SCAN           = 0.1
AIM_TURN_SPEED     = 110
AIM_MIN_TIME       = 0.15
AIM_MAX_TIME       = 0.80
AIM_RETRACK        = 2.5
AIM_JITTER         = 0.8
AIM_JITTER_TIME    = 0.40
AIM_JITTER_MIN     = 1.0
AIM_JITTER_MAX     = 3.0
AIM_PITCH          = "auto"  # "auto" = aim at the warden's body (needed for a bow, arrows fly in an arc)
                             # a number = lock pitch to that value (0 = straight ahead)
                             # None = never touch pitch
AIM_TARGET_HEIGHT  = 1.6     # "auto": aim this many blocks above the warden's feet
AIM_PITCH_OFFSET   = 0.0     # "auto": extra pitch in degrees (negative = aim higher, to compensate arrow drop at range)
AIM_PITCH_JITTER   = 0.25    # extra DOWNWARD wobble only (degrees), never up. 0 = off
AIM_PITCH_MIN      = -10.0   # never aim higher than this (negative = up), so pitch is never above -10

# Strafe (left 1s, right 1s)
STRAFE             = True
STRAFE_EVERY       = 20
STRAFE_TIME        = 1.0
STRAFE_SETTLE      = 0.6

# Bow
AUTO_BOW           = True    # switch to a bow in the hotbar automatically
BOW_CHECK          = 0.5
NEED_ARROWS        = True    # don't draw if there are no arrows in the inventory
AMMO_KEYWORD       = "arrow"

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
AUTO_CLICK   = True          # auto-shoot on at start
DEBUG        = False
STATUS       = True
TAG = "[AutoBow]"

# GLFW key codes
CLICK_KEY  = 295   # F6  toggle auto-shoot
TOGGLE_KEY = 296   # F7  pause
FEED_KEY   = 297   # F8  auto-feed
STOP_KEY   = 298   # F9  stop the script
ALARM_OFF_KEY = 80 # P   silence the alarm

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
click_method = None

# ── State ─────────────────────────────────────────────────────────────────────
stopped = False
paused = START_PAUSED
alarm_on = False
disconnecting = False
auto_click_on = AUTO_CLICK
auto_feed_on = AUTO_FEED

next_feed_t = 0.0

last_bow_check = 0.0
bow_ok = False
last_bow_warn = 0.0
last_ammo_warn = 0.0

ac_next_t = 0.0
ac_release_t = 0.0           # when the current draw ends (0 = not drawing)
ac_base = None
origin_pos = None
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
hotbar_base = None
players_alerted = set()
WL = set(n.lower() for n in PLAYER_WHITELIST)

strafe_state = "idle"
strafe_until = 0.0
next_strafe_t = 0.0
strafe_settle_until = 0.0

aim_pos = None               # (x, y, z) of the warden we are following
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

MSG_RE = re.compile("MSG \\((.+?)\\s*➜\\s*me\\)", re.I)

def press_use(state):
    # right click (use item): hold = draw the bow, release = shoot
    try:
        minescript.player_press_use(state)
    except Exception:
        try:
            minescript.press_key_bind("key.use", state)
        except Exception as e:
            say("right-click failed: " + str(e))

def release_use():
    global ac_release_t
    ac_release_t = 0.0
    press_use(False)

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
    release_use()
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
        release_use()
        say("AFK check detected: " + str(len(targets)) + " target(s), auto-shoot paused")
        return

    if not gui:
        afk_active = False
        afk_hold_until = 0.0
        afk_clicked.clear()
        say("AFK check done, auto-shoot resumes")
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

# ── Bow / ammo ────────────────────────────────────────────────────────────────
def _is_bow(name):
    name = str(name).lower()
    return name.endswith(":bow") or name == "bow"      # not crossbow

def holding_bow():
    try:
        mh = minescript.player_hand_items().main_hand
        return mh is not None and _is_bow(mh.item)
    except Exception:
        return True

def find_bow_slot():
    try:
        inv = minescript.player_inventory()
    except Exception:
        return None
    for it in inv:
        if it.slot is None or not (0 <= it.slot <= 8):
            continue
        if _is_bow(it.item):
            return it.slot
    return None

def has_arrows():
    if not NEED_ARROWS:
        return True
    try:
        inv = minescript.player_inventory()
    except Exception:
        return True
    for it in inv or []:
        if AMMO_KEYWORD in str(it.item).lower():
            return True
    return False

def ensure_bow(t):
    global last_bow_check, bow_ok, last_bow_warn, ac_was_blocked
    if not AUTO_BOW:
        return True
    if t - last_bow_check < BOW_CHECK:
        return bow_ok
    last_bow_check = t

    if holding_bow():
        bow_ok = True
        return True

    bow_ok = False
    slot = find_bow_slot()
    if slot is None:
        if t - last_bow_warn > 10:
            say("No bow in the hotbar - not shooting")
            last_bow_warn = t
        return False
    try:
        minescript.player_inventory_select_slot(slot)
        say("Switched to bow (slot " + str(slot) + ")")
        ac_was_blocked = True
    except Exception as e:
        say("Can't select bow slot: " + str(e))
    return False

# ── Target check (warden under the crosshair) ────────────────────────────────
def _is_warden(text):
    text = str(text).lower()
    return "warden" in text and "armor" not in text

def target_seen():
    desc = []
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

# ── Smooth aim ────────────────────────────────────────────────────────────────
def _fallback_look(yaw, pitch, duration):
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
    global look_thread
    def run():
        try:
            do_smooth_look(yaw, pitch, duration)
        except Exception as e:
            dbg("look thread error: " + str(e))
    look_thread = threading.Thread(target=run, daemon=True)
    look_thread.start()

def scan_warden(yaw, mypos):
    # nearest-to-crosshair warden inside the front cone, as (x, y, z) or None
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
            continue
        if best is None or diff < best_diff:
            best = (e.position[0], e.position[1], e.position[2])
            best_diff = diff
    return best

def aim_pitch_for(mypos, pitch_now):
    # pitch (degrees, positive = down) to use for the current target
    if AIM_PITCH is None:
        return pitch_now
    if AIM_PITCH == "auto" and aim_pos is not None:
        dx = aim_pos[0] - mypos[0]
        dz = aim_pos[2] - mypos[2]
        horiz = math.sqrt(dx * dx + dz * dz)
        dy = (aim_pos[1] + AIM_TARGET_HEIGHT) - (mypos[1] + 1.62)
        base = -math.degrees(math.atan2(dy, max(horiz, 0.01))) + AIM_PITCH_OFFSET
    elif isinstance(AIM_PITCH, (int, float)):
        base = float(AIM_PITCH)
    else:
        return pitch_now
    return clamp(base + random.uniform(0.0, AIM_PITCH_JITTER), AIM_PITCH_MIN, 89.0)

def aim_tick(t):
    global aim_pos, aim_next_scan, aim_next_move_t
    if not AIM or not auto_click_on or blocked_reason(t) is not None:
        aim_pos = None
        look_cancel.set()
        return
    if look_thread is not None and look_thread.is_alive():
        return
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
        return

    dx = aim_pos[0] - mypos[0]
    dz = aim_pos[2] - mypos[2]
    if dx * dx + dz * dz < 0.01:
        return
    base = math.degrees(math.atan2(-dx, dz))
    target_pitch = aim_pitch_for(mypos, pitch)
    off_target = (abs(wrap180(base - yaw)) > AIM_RETRACK or
                  (AIM_PITCH is not None and abs(target_pitch - pitch) > AIM_RETRACK + AIM_PITCH_JITTER))
    if not off_target and t < aim_next_move_t:
        return

    dyaw = wrap180(base + random.uniform(-AIM_JITTER, AIM_JITTER) - yaw)
    if off_target:
        duration = clamp(max(abs(dyaw), abs(target_pitch - pitch)) / AIM_TURN_SPEED,
                         AIM_MIN_TIME, AIM_MAX_TIME) * random.uniform(0.9, 1.2)
    else:
        duration = AIM_JITTER_TIME
    aim_next_move_t = t + random.uniform(AIM_JITTER_MIN, AIM_JITTER_MAX)
    start_look(yaw + dyaw, target_pitch, duration)

# ── Strafe ────────────────────────────────────────────────────────────────────
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

# ── Auto-shoot (hold right click, release) ───────────────────────────────────
def autoclick_tick(t):
    global ac_next_t, ac_release_t, ac_base, ac_was_blocked, auto_click_on, origin_pos
    global last_ammo_warn

    # finish the current draw: letting go of right click fires the arrow
    if ac_release_t and t >= ac_release_t:
        release_use()

    if not auto_click_on:
        status("auto-shoot is OFF (F6 or left click to turn on)")
        return

    if autoclick_blocked(t):
        if ac_release_t:
            release_use()
        ac_was_blocked = True
        return

    if not ensure_bow(t):
        status("no bow in hand / switching")
        if ac_release_t:
            release_use()
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

    if strafe_state == "idle" and t >= strafe_settle_until:
        dist = sum((a - b) ** 2 for a, b in zip(pos, origin_pos)) ** 0.5
        if dist >= MOVE_ALARM_BLOCKS:
            release_use()
            msg = ("Moved " + str(round(dist, 1)) + " blocks from the original position " +
                   str([round(c, 1) for c in origin_pos]))
            say(msg)
            if MOVE_ALARM:
                trigger_alarm(msg)
            else:
                origin_pos = pos
            return

    # a draw already in progress is always finished (so the arrow actually fires)
    if ac_release_t:
        return

    if t < ac_next_t:
        return

    # only start drawing while a warden is under the crosshair
    if not looking_at_warden():
        return

    if not has_arrows():
        if t - last_ammo_warn > 10:
            say("No arrows in the inventory - not shooting")
            last_ammo_warn = t
        return

    status("drawing bow")
    press_use(True)
    ac_release_t = t + random.uniform(DRAW_MIN, DRAW_MAX)
    ac_next_t = ac_release_t + random.uniform(SHOT_GAP_MIN, SHOT_GAP_MAX)

# ── Player proximity ──────────────────────────────────────────────────────────
def nearby_players():
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
            players_alerted.discard(name)
    for name, d in near.items():
        if name not in players_alerted:
            players_alerted.add(name)
            trigger_alarm("Player nearby: " + name + " (" + str(round(d, 1)) + " blocks)")

# ── Hotbar change ─────────────────────────────────────────────────────────────
def hotbar_snapshot():
    # {slot: (item, count)} for hotbar slots 0-8; count is 0 for items in HOTBAR_IGNORE_COUNT
    inv = minescript.player_inventory()
    snap = {}
    for it in inv or []:
        if it.slot is None or not (0 <= it.slot <= 8):
            continue
        name = str(it.item)
        count = getattr(it, "count", 1)
        if any(k in name for k in HOTBAR_IGNORE_COUNT):
            count = 0
        snap[it.slot] = (name, count)
    return snap

def _ignored_item(name):
    return any(k in name for k in HOTBAR_IGNORE_ADDED)

def hotbar_pure_add(old, new):
    if new is None or not _ignored_item(new[0]):
        return False
    if old is None:
        return True
    return old[0] == new[0] and new[1] > old[1]

def hotbar_tick(t):
    global last_hotbar_check, hotbar_base
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
                continue
            f = lambda v: "empty" if v is None else str(v[1]) + "x " + v[0].replace("minecraft:", "")
            changes.append("slot " + str(slot + 1) + ": " + f(old) + " -> " + f(new))
    hotbar_base = snap
    if not changes:
        return
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
        release_use()
        strafe_stop()
        say("AFK check announced, auto-shoot paused")
        return

    if TPMSG_ALARM and not paused and auto_click_on:
        if TPMSG_RE.search(message):
            trigger_alarm("Teleported: " + message.strip()[:80])
            return

    if MSG_ALARM and not paused and auto_click_on:
        m = MSG_RE.search(message)
        if m:
            sender = m.group(1).strip()
            if MSG_IGNORE_WHITELIST and sender.lower() in WL:
                return
            trigger_alarm("MSG from " + sender)

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
        if alarm_on and minescript.screen_name() is None:
            alarm_on = False
            ac_was_blocked = True
            origin_pos = None
            say("Alarm silenced" +
                ("" if auto_click_on else " - auto-shoot is still OFF (F6 or left click)"))
        return
    if alarm_on and event.key in (TOGGLE_KEY, CLICK_KEY) and minescript.screen_name() is None:
        alarm_on = False
    if minescript.screen_name() is not None or alarm_on:
        return
    if event.key == TOGGLE_KEY:
        paused = not paused
        if paused:
            release_use()
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
            release_use()
            strafe_stop()
        say("Auto-shoot " + ("ON" if auto_click_on else "OFF"))

def on_mouse(event):
    global auto_click_on, ac_was_blocked, origin_pos
    if not LEFT_CLICK_ENABLES:
        return
    if event.button != 0 or event.action != 1:
        return
    if auto_click_on or alarm_on:
        return
    if minescript.screen_name() is not None:
        return
    auto_click_on = True
    origin_pos = None
    ac_was_blocked = True
    say("Auto-shoot ON (left click)")

# ── Main loop ─────────────────────────────────────────────────────────────────
def main():
    global next_feed_t, next_strafe_t
    say("Loaded. " + ("PAUSED - press F7. " if paused else "") +
        "F6 auto-shoot, F7 pause, F8 auto-feed, P silence alarm, F9 stop, "
        "left click re-enables. Auto-shoot " +
        ("ON" if auto_click_on else "OFF") + ", auto-feed " + ("ON" if auto_feed_on else "OFF") +
        " (" + FEED_COMMAND + " every " + str(FEED_EVERY) + "s). Alarm action: " + ALARM_ACTION +
        ". Aim " + ("ON" if AIM else "OFF") +
        ", strafe " + ("every " + str(STRAFE_EVERY) + "s" if STRAFE else "OFF"))
    if ClickEnum is None:
        say("WARNING: click class not found; GUI clicking will fail (alarm will sound).")

    bslot = find_bow_slot()
    say("Check: bow slot " + ("NONE FOUND in hotbar" if bslot is None else str(bslot)) +
        ", arrows " + ("found" if has_arrows() else "NOT FOUND"))

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
            release_use()
            strafe_stop()
            say("STOPPED")

main()