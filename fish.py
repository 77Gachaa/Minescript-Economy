# strafe_afk_v2.py - Minescript (Python)
# ---------------------------------------------------------------
#   ORIGIN:    the spot where you run the script is the origin (no fixed coords).
#   MOVEMENT:  every MOVE_INTERVAL seconds it holds S + A (left) or S + D (right)
#              for MOVE_HOLD seconds, then stops. Each interval alternates sides.
#              "Left/right" is relative to the direction you are facing.
#   LOOK:      every ~30s (random 20-40s) the view is nudged a few degrees
#              up/down/left/right using the smooth human look library. Offsets
#              are relative to the view you had when the origin was set (F8),
#              so it never drifts away.
#   AUTO-CAST: if there's no fishing bobber (e.g. the AFK check removed it), it
#              right-clicks (use key, so the hand swings) to cast again.
#   TURTLE:    if a turtle is within TURTLE_RANGE (3) blocks -> reel in the rod,
#              smooth-look at the turtle and hit it (only while it is within
#              range) until it is gone, then smooth-look back to the saved
#              yaw/pitch and cast the rod again.
#   ANTI-AFK:  clicks every "Click me" item in the AFK GUI (movement freezes
#              during the AFK check).
#   PROXIMITY: any player NOT on WHITELIST within PROXIMITY_RADIUS blocks ->
#              movement freezes and a beep alarm plays (winsound) until the
#              job is suspended (\suspend) or stopped (F9 / \killjob).
#   TELEPORT:  if you end up far from the origin (teleported / pushed away),
#              or your position jumps suddenly -> same beep alarm.
#   MSG:       a private message sent to you ("MSG (Name ➜ me) • text") ->
#              same beep alarm. Nothing ever disconnects you.
#
# SETUP: save the smooth look library as  smooth_look.py  in the same folder as
#        this script (or change LOOK_MODULE below to its file name, no .py).
#
# Run:  \strafe_afk_v2
# Keys: F4 turtle hunt on/off, F6 movement on/off, F7 pause/resume,
#       F8 set new origin here, F9 stop, F10 proximity on/off,
#       F11 auto-cast on/off, F12 look on/off

import importlib
import math
import os
import queue
import random
import re
import time

import minescript
from java import JavaClass

try:
    import winsound
except Exception:
    winsound = None

# ── SETTINGS ──────────────────────────────────────────────────────────────────
MOVE_INTERVAL   = 20.0    # seconds between moves (sides alternate each time)
MOVE_HOLD       = 1.0     # seconds to hold S + A / S + D
START_DELAY     = 3.0     # seconds before the first move
START_SIDE      = +1      # +1 = start with left, -1 = start with right

# Subtle look movement (uses the smooth look library)
LOOK_ENABLED      = True
LOOK_MODULE       = "smooth_look"   # file name of the look library (no .py)
LOOK_INTERVAL_MIN = 15.0            # random wait between nudges (seconds)
LOOK_INTERVAL_MAX = 20.0            # (average ~30s)
LOOK_YAW_MIN      = 1.0             # left/right offset range in degrees
LOOK_YAW_MAX      = 2.5
LOOK_PITCH_MIN    = 0.5             # up/down offset range in degrees
LOOK_PITCH_MAX    = 2.5
LOOK_MAX_PITCH    = 70.0            # never look further up/down than this
LOOK_URGENT       = 0.0             # 0 = slow and smooth, 1 = fast

# Auto-cast (no bobber -> use key, real hand swing)
AUTOCAST_ENABLED = True
RECAST_DELAY     = 1.5    # no bobber for this long (while not frozen) -> cast
CAST_HOLD        = 0.12   # how long the use key is held (seconds)
CAST_COOLDOWN    = 3.0    # minimum time between casts
REQUIRE_ROD      = True   # only cast if a fishing rod is in the main hand

# Turtle hunt: turtle within range -> stop fishing, hit it, look back, recast
TURTLE_ENABLED        = True
TURTLE_RANGE          = 3.0    # only react to / hit turtles within this many blocks
TURTLE_CHECK          = 0.25   # seconds between turtle scans while fishing
TURTLE_LOOK_URGENT    = 0.5    # smooth look speed when aiming at the turtle (0-1)
TURTLE_AIM_TOL        = 4.0    # degrees of aim error allowed before swinging
TURTLE_AIM_INTERVAL   = 0.35   # re-aim at the turtle at most this often (seconds)
TURTLE_ATTACK_MIN     = 0.55   # random delay between swings (seconds)
TURTLE_ATTACK_MAX     = 0.80
TURTLE_ATTACK_HOLD    = 0.10   # how long the attack key is held per swing
TURTLE_GONE_WAIT      = 1.5    # no turtle in range for this long = it's gone
TURTLE_MAX_FIGHT      = 40.0   # give up after this many seconds and go back
TURTLE_REEL_TIMEOUT   = 3.0    # max wait for the bobber to be reeled in
TURTLE_RETURN_TIMEOUT = 6.0    # max wait for the look-back to finish
TURTLE_RETURN_TOL     = 1.5    # degrees: close enough to the saved yaw/pitch
TURTLE_COOLDOWN       = 2.0    # pause before scanning for turtles again
TURTLE_WEAPON_SLOT    = None   # hotbar slot 0-8 to hit with (None = keep the rod)
EYE_HEIGHT            = 1.62   # player eye height above feet

# Proximity -> sound alarm
PROXIMITY_ENABLED = True
PROXIMITY_RADIUS  = 20.0
PROXIMITY_CHECK   = 0.1
WHITELIST = [             # case-insensitive
    "Ivaniam",
    "Westl1fe",
    "Svea",
    "014k",
    "LexQiqi",
    "KrissS0_0"
]
BEEP_FREQS    = (1000, 1600)   # alternating beep pitches (Hz)
BEEP_MS       = 250            # length of each beep
BEEP_GAP      = 0.15           # pause between beeps (seconds)
SUSPEND_GAP   = 1.5            # loop stalled this long = job was suspended -> clear alarm

# Teleport / moved-away alarm
LEAVE_ENABLED = True
LEAVE_RADIUS  = 8.0       # blocks from the origin (horizontal) before alarming
LEAVE_Y       = 5.0       # blocks of height difference before alarming
JUMP_DISTANCE = 6.0       # sudden horizontal jump between two checks = teleport
POS_CHECK     = 0.1       # seconds between position checks

# Private-message alarm (matches e.g. "MSG (Ivaniam ➜ me) • hello")
MSG_ALARM            = True
MSG_IGNORE_WHITELIST = False   # True = whitelisted senders don't trigger it

# Anti-AFK
AFK_PHRASES      = ["afk check"]
AFK_HOLD_SECONDS = 6
AFK_OPEN_WAIT    = 0.15
AFK_CLICK_MIN    = 0.12
AFK_CLICK_MAX    = 0.35
AFK_GUI_TIMEOUT  = 55

START_PAUSED = False
MOVE_ON      = True
DEBUG        = False
TAG = "[Strafe]"

# GLFW key codes
TURTLE_KEY    = 293   # F4
MOVE_KEY      = 295   # F6
TOGGLE_KEY    = 296   # F7
ORIGIN_KEY    = 297   # F8
STOP_KEY      = 298   # F9
PROXIMITY_KEY = 299   # F10
CAST_KEY      = 300   # F11
LOOK_KEY      = 301   # F12

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

# ── Smooth look library ───────────────────────────────────────────────────────
human_look = None
look_import_error = ""
try:
    human_look = importlib.import_module(LOOK_MODULE)
except Exception as e:
    look_import_error = str(e)

# ── State ─────────────────────────────────────────────────────────────────────
stopped = False
paused = START_PAUSED
alarm_on = False         # proximity alarm: beeping + movement frozen
afk_failed = False       # AFK GUI could not be handled
move_on = MOVE_ON
proximity_on = PROXIMITY_ENABLED
autocast_on = AUTOCAST_ENABLED
look_on = LOOK_ENABLED
turtle_on = TURTLE_ENABLED

last_prox_check = 0.0
WHITELIST_LOWER = set(n.strip().lower() for n in WHITELIST)

# teleport detection
away_latched = False     # True after a teleport alarm until you're back / press F8
last_pos = None
last_pos_check = 0.0

# sound
next_beep_t = 0.0
beep_i = 0

# origin / movement
origin_x = 0.0
origin_y = 0.0
origin_z = 0.0
in_pattern = False
step_active = False      # keys currently held
move_start_t = 0.0
move_side = START_SIDE
next_pattern_t = 0.0
last_move_tick = 0.0
last_loop_t = 0.0

# look
base_yaw = 0.0
base_pitch = 0.0
next_look_t = 0.0
last_look_tick = 0.0

# auto-cast
no_bobber_since = None
cast_pressed = False
cast_release_t = 0.0
next_cast_t = 0.0

# turtle hunt
turtle_state = None      # None | "reel" | "fight" | "return"
turtle_t0 = 0.0          # when the current stage started
turtle_fight_t0 = 0.0
turtle_gone_since = None
turtle_reel_sent = False
turtle_prev_slot = None
turtle_last_look = 0.0
next_turtle_check = 0.0
next_aim_t = 0.0
next_attack_t = 0.0
attack_pressed = False
attack_release_t = 0.0
last_turtle_tick = 0.0

# anti-afk
afk_active = False
afk_open_t = 0.0
afk_hold_until = 0.0
afk_next_click_t = 0.0
afk_clicked = set()

last_chat_norm = ""
last_chat_t = 0.0

# ── Helpers ───────────────────────────────────────────────────────────────────
def say(text):
    minescript.echo(TAG + " " + text)

def dbg(text):
    if DEBUG:
        say("(dbg) " + text)

def norm(s):
    s = str(s).lower()
    s = re.sub(r"\u00a7.", "", s)
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return " ".join(s.split())

NAFK = [norm(p) for p in AFK_PHRASES]

def gui_is_open():
    s = minescript.screen_name()
    return s is not None and "chat" not in str(s).lower()

def release_keys():
    for fn in (minescript.player_press_backward,
               minescript.player_press_left,
               minescript.player_press_right):
        try:
            fn(False)
        except Exception:
            pass

def release_use():
    try:
        minescript.player_press_use(False)
    except Exception:
        pass

def release_attack():
    try:
        minescript.player_press_attack(False)
    except Exception:
        pass

def hold_keys(direction):
    """S + A for left (+1), S + D for right (-1). Backward is ALWAYS held."""
    try:
        minescript.player_press_backward(True)
        minescript.player_press_left(direction > 0)
        minescript.player_press_right(direction < 0)
    except Exception as e:
        say("key press failed: " + str(e))

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

# ── Alarm (beeps from the main loop, so a suspended job goes quiet) ──────────
def trigger_alarm(reason):
    global alarm_on, next_beep_t
    if alarm_on:
        return
    release_keys()
    release_attack()
    alarm_on = True
    next_beep_t = 0.0
    try:
        minescript.echo_json({
            "text": TAG + " ALARM: " + reason + "  (\\suspend or F9 to silence)",
            "color": "red"})
    except Exception:
        say("ALARM: " + reason + "  (\\suspend or F9 to silence)")

def alarm_tick(t):
    global next_beep_t, beep_i
    if not alarm_on or stopped:
        return
    if t < next_beep_t:
        return
    if winsound is None:
        next_beep_t = t + 5
        say("winsound not available (Windows only) - no sound!")
        return
    try:
        winsound.Beep(BEEP_FREQS[beep_i % len(BEEP_FREQS)], BEEP_MS)
    except Exception as e:
        dbg("beep failed: " + str(e))
    beep_i += 1
    next_beep_t = time.time() + BEEP_GAP

# ── Proximity check ──────────────────────────────────────────────────────────
def proximity_tick(t):
    global last_prox_check
    if not proximity_on or alarm_on:
        return
    if t - last_prox_check < PROXIMITY_CHECK:
        return
    last_prox_check = t
    try:
        nearby = minescript.players(max_distance=PROXIMITY_RADIUS)
    except Exception as e:
        dbg("players() failed: " + str(e))
        return
    try:
        my_name = str(minescript.player_name()).lower()
    except Exception:
        my_name = ""
    for p in nearby:
        if getattr(p, "local", False):
            continue
        name = str(p.name)
        low = name.lower()
        if low == my_name or low in WHITELIST_LOWER:
            continue
        trigger_alarm(name + " is within " + str(int(PROXIMITY_RADIUS)) + " blocks")
        return

# ── Teleport / moved-away check ──────────────────────────────────────────────
def teleport_tick(t):
    global last_pos, last_pos_check, away_latched
    global in_pattern, step_active, next_pattern_t
    if not LEAVE_ENABLED:
        return
    if t - last_pos_check < POS_CHECK:
        return
    last_pos_check = t
    try:
        pos = minescript.player_position()
    except Exception:
        return
    x, y, z = pos[0], pos[1], pos[2]
    prev = last_pos
    last_pos = (x, y, z)

    dist = math.hypot(x - origin_x, z - origin_z)
    dy = abs(y - origin_y)
    inside = dist <= LEAVE_RADIUS and dy <= LEAVE_Y

    if away_latched:
        if inside:
            away_latched = False
            say("Back inside the area, movement can continue")
        return
    if alarm_on and inside:
        return

    reason = None
    if prev is not None and math.hypot(x - prev[0], z - prev[2]) >= JUMP_DISTANCE:
        reason = "Sudden position jump (teleport?)"
    elif not inside:
        reason = "Moved away from the origin (%.1f blocks)" % dist
    if reason is None:
        return

    # abort the current move, freeze movement until you're back or press F8
    away_latched = True
    in_pattern = False
    step_active = False
    next_pattern_t = t + MOVE_INTERVAL
    trigger_alarm(reason + " - X %.1f Y %.1f Z %.1f" % (x, y, z))
    say("Movement frozen. Go back to the origin or press F8 to set a new one here.")

# ── Private message check ────────────────────────────────────────────────────
# "MSG (Sender <arrow> me) ..."  - only messages TO you ("... me)") match.
MSG_RE = re.compile(r"MSG\s*\(\s*([^\s()]+)\s*\S+\s*me\s*\)", re.IGNORECASE)

def check_msg(message):
    if not MSG_ALARM:
        return
    m = MSG_RE.search(message)
    if not m:
        return
    sender = m.group(1)
    if MSG_IGNORE_WHITELIST and sender.lower() in WHITELIST_LOWER:
        return
    trigger_alarm("Private message from " + sender)

# ── Anti-AFK ─────────────────────────────────────────────────────────────────
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

def click_slot(slot):
    mc = Minecraft.getInstance()
    player = mc.player
    cid = player.containerMenu.containerId
    gm = mc.gameMode
    last = None
    for method in ("handleContainerInput", "handleInventoryMouseClick"):
        try:
            getattr(gm, method)(cid, slot, 0, ClickEnum.PICKUP, player)
            return True
        except Exception as e:
            last = e
    say("click failed: " + str(last))
    return False

def afk_fail(reason):
    global afk_failed
    afk_failed = True
    trigger_alarm(reason)

def afk_tick(t):
    global afk_active, afk_open_t, afk_next_click_t, afk_hold_until
    if afk_failed:
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
        release_keys()
        say("AFK check detected: " + str(len(targets)) + " target(s), movement frozen")
        return

    if not gui:
        afk_active = False
        afk_hold_until = 0.0
        afk_clicked.clear()
        say("AFK check done, movement continues")
        return

    if t - afk_open_t > AFK_GUI_TIMEOUT:
        afk_fail("AFK GUI still open after " + str(AFK_GUI_TIMEOUT) + "s")
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
            afk_fail("Could not click the AFK item (click method failed)")
        return

# ── Auto-cast (use key -> real hand swing, no packets) ───────────────────────
def has_bobber():
    """True if our fishing bobber is out. Uses player.fishing, falls back to entities."""
    try:
        return Minecraft.getInstance().player.fishing is not None
    except Exception:
        pass
    try:
        for e in minescript.entities(max_distance=40):
            if "fishing_bobber" in str(e.type).lower():
                return True
    except Exception as e:
        dbg("bobber check failed: " + str(e))
    return False

def holding_rod():
    if not REQUIRE_ROD:
        return True
    try:
        hands = minescript.player_hand_items()
        main = hands.main_hand
        return main is not None and "fishing_rod" in str(main.item).lower()
    except Exception:
        return True   # can't tell -> don't block casting

def pulse_use(t):
    """Tap the use key (cast, or reel in if the bobber is out). Released by cast_tick."""
    global cast_pressed, cast_release_t
    minescript.player_press_use(True)
    cast_pressed = True
    cast_release_t = t + CAST_HOLD

def cast_tick(t):
    global no_bobber_since, cast_pressed, cast_release_t, next_cast_t

    # finish a cast: release the use key
    if cast_pressed:
        if t >= cast_release_t:
            release_use()
            cast_pressed = False
            next_cast_t = t + CAST_COOLDOWN
        return

    if not autocast_on:
        no_bobber_since = None
        return

    blocked = (paused or alarm_on or away_latched or afk_active
               or t < afk_hold_until or turtle_state is not None
               or minescript.screen_name() is not None)
    if blocked:
        no_bobber_since = None     # must be clear for RECAST_DELAY after it ends
        return

    if has_bobber():
        no_bobber_since = None
        return

    if not holding_rod():
        no_bobber_since = None
        return

    if no_bobber_since is None:
        no_bobber_since = t
        return

    if t - no_bobber_since < RECAST_DELAY or t < next_cast_t:
        return

    try:
        pulse_use(t)
        no_bobber_since = None
        say("No bobber - casting")
    except Exception as e:
        say("cast failed: " + str(e))
        next_cast_t = t + CAST_COOLDOWN

# ── Smooth look helpers ──────────────────────────────────────────────────────
def wrap180(a):
    return (a + 180.0) % 360.0 - 180.0

def look_to(yaw, pitch, urgent):
    """Smooth look to (yaw, pitch) via the look library; falls back to a snap.
    Yaw is re-expressed relative to the current view so it takes the short way round."""
    try:
        o = minescript.player_orientation()
        cur_yaw = float(o[0])
    except Exception:
        cur_yaw = yaw
    yaw = cur_yaw + wrap180(yaw - cur_yaw)
    pitch = max(-90.0, min(90.0, pitch))
    if human_look is not None:
        try:
            human_look.look(yaw, pitch, urgent=urgent)
            return
        except Exception as e:
            dbg("smooth look failed: " + str(e))
    try:
        minescript.player_set_orientation(yaw, pitch)
    except Exception as e:
        dbg("set orientation failed: " + str(e))

def angle_error(yaw, pitch):
    """Largest of the yaw / pitch differences (degrees) from the current view."""
    o = minescript.player_orientation()
    return max(abs(wrap180(yaw - float(o[0]))), abs(pitch - float(o[1])))

# ── Turtle hunt ──────────────────────────────────────────────────────────────
def find_turtles(max_dist):
    """Living turtles within max_dist blocks, nearest first."""
    try:
        found = minescript.entities(type=".*turtle.*", max_distance=max_dist,
                                    sort="nearest", limit=3)
    except Exception as e:
        dbg("turtle scan failed: " + str(e))
        return []
    out = []
    for e in found or []:
        if "turtle" not in str(e.type).lower():
            continue
        hp = getattr(e, "health", None)
        if hp is not None and hp <= 0:      # dying -> counts as gone
            continue
        out.append(e)
    return out

def angles_to(e):
    """Yaw / pitch needed to look at the middle of the turtle."""
    px, py, pz = minescript.player_position()[:3]
    tx, ty, tz = e.position[0], e.position[1], e.position[2]
    dx = tx - px
    dz = tz - pz
    dy = (ty + 0.2) - (py + EYE_HEIGHT)
    yaw = math.degrees(math.atan2(-dx, dz))
    pitch = -math.degrees(math.atan2(dy, math.hypot(dx, dz)))
    return yaw, pitch

def crosshair_on_turtle():
    try:
        te = minescript.player_get_targeted_entity(max_distance=TURTLE_RANGE + 1.0)
    except Exception:
        return True          # can't tell -> rely on the aim error alone
    return te is not None and "turtle" in str(te.type).lower()

def select_weapon():
    global turtle_prev_slot
    if TURTLE_WEAPON_SLOT is None:
        return
    try:
        turtle_prev_slot = minescript.player_inventory_select_slot(TURTLE_WEAPON_SLOT)
    except Exception as e:
        dbg("weapon select failed: " + str(e))

def restore_slot():
    global turtle_prev_slot
    if turtle_prev_slot is None:
        return
    try:
        minescript.player_inventory_select_slot(turtle_prev_slot)
    except Exception as e:
        dbg("slot restore failed: " + str(e))
    turtle_prev_slot = None

def end_attack():
    global attack_pressed
    release_attack()
    attack_pressed = False

def abort_turtle(t):
    """Drop out of the turtle routine without recasting (autocast takes over)."""
    global turtle_state, next_turtle_check
    end_attack()
    restore_slot()
    turtle_state = None
    next_turtle_check = t + TURTLE_COOLDOWN

def start_return(t):
    global turtle_state, turtle_t0, turtle_last_look
    end_attack()
    restore_slot()
    turtle_state = "return"
    turtle_t0 = t
    turtle_last_look = t
    look_to(base_yaw, base_pitch, TURTLE_LOOK_URGENT)
    say("Looking back at the saved view")

def finish_turtle(t):
    global turtle_state, next_turtle_check, no_bobber_since
    turtle_state = None
    next_turtle_check = t + TURTLE_COOLDOWN
    no_bobber_since = None
    schedule_next_look(time.time())
    if cast_pressed:
        return
    try:
        if not has_bobber() and holding_rod():
            pulse_use(t)
            say("Casting the rod again")
    except Exception as e:
        say("recast failed: " + str(e))

def turtle_tick(t):
    global turtle_state, turtle_t0, turtle_fight_t0, turtle_gone_since
    global turtle_reel_sent, turtle_last_look, next_turtle_check
    global next_aim_t, next_attack_t, attack_pressed, attack_release_t
    global last_turtle_tick

    dt = t - last_turtle_tick
    last_turtle_tick = t

    # let go of the attack key after each swing
    if attack_pressed and t >= attack_release_t:
        end_attack()

    blocked = (paused or alarm_on or away_latched or afk_active
               or t < afk_hold_until or minescript.screen_name() is not None)
    if blocked:
        if turtle_state is not None:
            end_attack()
            turtle_t0 += dt                # timers don't run down while blocked
            turtle_fight_t0 += dt
            if turtle_gone_since is not None:
                turtle_gone_since += dt
        return

    # switched off in the middle of a hunt
    if not turtle_on:
        if turtle_state is not None:
            say("Turtle hunt switched off - aborting")
            abort_turtle(t)
        return

    # ── idle: scan for a turtle in range ──
    if turtle_state is None:
        if t < next_turtle_check:
            return
        next_turtle_check = t + TURTLE_CHECK
        if not find_turtles(TURTLE_RANGE):
            return
        release_keys()
        turtle_state = "reel"
        turtle_t0 = t
        turtle_reel_sent = False
        say("Turtle within %d blocks - stopping fishing" % int(TURTLE_RANGE))
        return

    # ── stage 1: reel the bobber in ──
    if turtle_state == "reel":
        if cast_pressed:
            return
        if has_bobber() and t - turtle_t0 < TURTLE_REEL_TIMEOUT:
            if not turtle_reel_sent:
                try:
                    pulse_use(t)
                except Exception as e:
                    dbg("reel failed: " + str(e))
                turtle_reel_sent = True
            return
        select_weapon()
        turtle_state = "fight"
        turtle_fight_t0 = t
        turtle_gone_since = None
        next_aim_t = 0.0
        next_attack_t = t + 0.3
        say("Attacking the turtle")
        return

    # ── stage 2: smooth-look at the turtle and hit it until it's gone ──
    if turtle_state == "fight":
        if t - turtle_fight_t0 > TURTLE_MAX_FIGHT:
            say("Turtle fight timed out - going back")
            start_return(t)
            return

        found = find_turtles(TURTLE_RANGE)
        if not found:
            if turtle_gone_since is None:
                turtle_gone_since = t
            elif t - turtle_gone_since >= TURTLE_GONE_WAIT:
                say("Turtle gone")
                start_return(t)
            return
        turtle_gone_since = None

        try:
            yaw, pitch = angles_to(found[0])
            err = angle_error(yaw, pitch)
        except Exception as e:
            dbg("aim calc failed: " + str(e))
            return

        if err > TURTLE_AIM_TOL:
            if t >= next_aim_t:
                look_to(yaw, pitch, TURTLE_LOOK_URGENT)
                next_aim_t = time.time() + TURTLE_AIM_INTERVAL
            return

        if attack_pressed or cast_pressed or t < next_attack_t:
            return
        if not crosshair_on_turtle():
            return
        try:
            minescript.player_press_attack(True)
            attack_pressed = True
            attack_release_t = t + TURTLE_ATTACK_HOLD
            next_attack_t = t + random.uniform(TURTLE_ATTACK_MIN, TURTLE_ATTACK_MAX)
        except Exception as e:
            say("attack failed: " + str(e))
            next_attack_t = t + 1.0
        return

    # ── stage 3: look back at the saved yaw/pitch, then cast again ──
    if turtle_state == "return":
        try:
            err = angle_error(base_yaw, base_pitch)
        except Exception:
            err = 0.0
        if err <= TURTLE_RETURN_TOL or t - turtle_t0 > TURTLE_RETURN_TIMEOUT:
            finish_turtle(t)
        elif t - turtle_last_look > 2.5:
            turtle_last_look = t
            look_to(base_yaw, base_pitch, TURTLE_LOOK_URGENT)

# ── Subtle look movement (smooth human look) ─────────────────────────────────
def schedule_next_look(now):
    global next_look_t
    next_look_t = now + random.uniform(LOOK_INTERVAL_MIN, LOOK_INTERVAL_MAX)

def read_base_orientation():
    """Remember the current view as the centre the nudges stay around."""
    global base_yaw, base_pitch
    try:
        o = minescript.player_orientation()
        base_yaw, base_pitch = float(o[0]), float(o[1])
    except Exception as e:
        dbg("orientation read failed: " + str(e))

def look_tick(t):
    global last_look_tick, next_look_t
    dt = t - last_look_tick
    last_look_tick = t

    if human_look is None:
        return

    blocked = ((not look_on) or paused or alarm_on or away_latched or afk_active
               or t < afk_hold_until or cast_pressed or in_pattern
               or turtle_state is not None
               or minescript.screen_name() is not None)
    if blocked:
        next_look_t += dt             # timer doesn't run down while blocked
        return

    if t < next_look_t:
        return

    # pick which axis/axes to nudge: left/right, up/down, or both
    mode = random.choice(("yaw", "pitch", "both"))
    yaw = base_yaw
    pitch = base_pitch
    if mode in ("yaw", "both"):
        yaw += random.choice((-1, 1)) * random.uniform(LOOK_YAW_MIN, LOOK_YAW_MAX)
    if mode in ("pitch", "both"):
        pitch += random.choice((-1, 1)) * random.uniform(LOOK_PITCH_MIN, LOOK_PITCH_MAX)
    pitch = max(-LOOK_MAX_PITCH, min(LOOK_MAX_PITCH, pitch))

    try:
        human_look.look(yaw, pitch, urgent=LOOK_URGENT)
        dbg("look nudge -> yaw %.1f pitch %.1f" % (yaw, pitch))
    except Exception as e:
        dbg("look failed: " + str(e))

    now = time.time()
    last_look_tick = now
    schedule_next_look(now)

# ── Movement: one side for MOVE_HOLD seconds, other side next interval ───────
def set_origin():
    """Remember where you stand as the origin (used by the teleport check)."""
    global origin_x, origin_y, origin_z, last_pos, away_latched
    pos = minescript.player_position()
    origin_x, origin_y, origin_z = pos[0], pos[1], pos[2]
    last_pos = (pos[0], pos[1], pos[2])
    away_latched = False
    read_base_orientation()
    say("Origin set at X %.2f Z %.2f" % (origin_x, origin_z))

def end_step():
    global step_active
    release_keys()
    step_active = False

def move_tick(t):
    global next_pattern_t, last_move_tick, in_pattern
    global step_active, move_start_t, move_side

    dt = t - last_move_tick
    last_move_tick = t

    frozen = ((not move_on) or paused or alarm_on or away_latched or afk_active
              or t < afk_hold_until or turtle_state is not None
              or minescript.screen_name() is not None)
    if frozen:
        next_pattern_t += dt          # timers don't run down
        move_start_t += dt
        if step_active:
            end_step()                # release keys; the hold resumes later
        return

    if not in_pattern:
        if t >= next_pattern_t:
            in_pattern = True
            step_active = False
            say("Move " + ("left" if move_side > 0 else "right"))
        return

    if not step_active:
        step_active = True
        move_start_t = t
        hold_keys(move_side)
        return

    if t - move_start_t >= MOVE_HOLD:
        end_step()
        in_pattern = False
        move_side = -move_side
        next_pattern_t = t + MOVE_INTERVAL
        say("Move done. Next (" + ("left" if move_side > 0 else "right") +
            ") in " + str(int(MOVE_INTERVAL)) + "s")
        return

    hold_keys(move_side)              # keep S + A/D held

# ── Events ────────────────────────────────────────────────────────────────────
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

    check_msg(message)

    if any(p in low for p in NAFK):
        afk_hold_until = time.time() + AFK_HOLD_SECONDS
        release_keys()
        say("AFK check announced, movement frozen")

def on_key(event):
    global stopped, paused, move_on, proximity_on, autocast_on, look_on, turtle_on
    if event.action != 1:
        return
    if DEBUG:
        say("(dbg) key code " + str(event.key))
    if event.key == STOP_KEY:
        stopped = True
        return
    if minescript.screen_name() is not None:
        return
    if event.key == TOGGLE_KEY:
        paused = not paused
        if paused:
            release_keys()
        say("PAUSED" if paused else "RUNNING")
    elif event.key == MOVE_KEY:
        move_on = not move_on
        if not move_on:
            release_keys()
        say("Movement " + ("ON" if move_on else "OFF"))
    elif event.key == ORIGIN_KEY:
        if not in_pattern:
            try:
                set_origin()
            except Exception as e:
                say("Can't set origin: " + str(e))
        else:
            say("Wait until the move finishes to set a new origin")
    elif event.key == PROXIMITY_KEY:
        proximity_on = not proximity_on
        say("Proximity alarm " + ("ON" if proximity_on else "OFF"))
    elif event.key == CAST_KEY:
        autocast_on = not autocast_on
        say("Auto-cast " + ("ON" if autocast_on else "OFF"))
    elif event.key == LOOK_KEY:
        look_on = not look_on
        if look_on:
            read_base_orientation()   # re-centre on where you're looking now
        say("Look movement " + ("ON" if look_on else "OFF"))
    elif event.key == TURTLE_KEY:
        turtle_on = not turtle_on
        say("Turtle hunt " + ("ON" if turtle_on else "OFF"))

# ── Main loop ─────────────────────────────────────────────────────────────────
def main():
    global next_pattern_t, last_move_tick, last_loop_t, alarm_on, last_look_tick
    global last_turtle_tick
    say("Loaded. " + ("PAUSED - press F7. " if paused else "") +
        "F4 turtle, F6 movement, F7 pause, F8 new origin, F9 stop, "
        "F10 proximity, F11 auto-cast, F12 look.")
    say("Movement: " + str(MOVE_HOLD) + "s on one side every " +
        str(int(MOVE_INTERVAL)) + "s, alternating left/right")
    if human_look is None:
        say("WARNING: look library '" + LOOK_MODULE + "' not found (" +
            look_import_error + ") - nudges disabled, turtle aiming will snap.")
    else:
        say("Look: " + ("ON" if look_on else "OFF") + ", nudge every " +
            str(int(LOOK_INTERVAL_MIN)) + "-" + str(int(LOOK_INTERVAL_MAX)) + "s, up to " +
            str(LOOK_YAW_MAX) + " deg yaw / " + str(LOOK_PITCH_MAX) + " deg pitch")
    say("Auto-cast: " + ("ON" if autocast_on else "OFF") +
        " (recast after " + str(RECAST_DELAY) + "s without a bobber)")
    say("Turtle hunt: " + ("ON" if turtle_on else "OFF") +
        ", reacts to turtles within " + str(TURTLE_RANGE) + " blocks")
    say("Proximity: " + ("ON" if proximity_on else "OFF") + ", radius " +
        str(PROXIMITY_RADIUS) + ", whitelist: " +
        (", ".join(WHITELIST) if WHITELIST else "(empty)"))
    say("Alarms: player within " + str(int(PROXIMITY_RADIUS)) + " blocks, " +
        "moved/teleported >" + str(int(LEAVE_RADIUS)) + " blocks from origin, " +
        "private message to you. (Beeps until \\suspend / F9, never disconnects.)")
    if winsound is None:
        say("WARNING: winsound not available - the alarm will be silent.")
    if ClickEnum is None:
        say("WARNING: click class not found; AFK clicking will fail.")

    try:
        set_origin()
    except Exception as e:
        say("Can't read start position: " + str(e))
        return

    now = time.time()
    next_pattern_t = now + START_DELAY
    last_move_tick = now
    last_loop_t = now
    last_look_tick = now
    last_turtle_tick = now
    schedule_next_look(now)

    log_open()
    with minescript.EventQueue() as events:
        events.register_chat_listener()
        events.register_key_listener()
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
                    elif et == minescript.EventType.WORLD:
                        if not ev.connected:
                            trigger_alarm("Disconnected from the server")
                    try:
                        ev = events.get(block=False)
                    except queue.Empty:
                        ev = None
                if stopped:
                    break

                t = time.time()

                # The loop stalled: the job was suspended and has now resumed.
                # Silence the alarm (it re-triggers if the player is still there).
                if alarm_on and t - last_loop_t > SUSPEND_GAP:
                    alarm_on = False
                    say("Job resumed - alarm cleared")
                last_loop_t = t

                proximity_tick(t)      # always runs, even when paused
                teleport_tick(t)
                alarm_tick(t)
                if stopped:
                    break

                log_tick()
                afk_tick(t)
                turtle_tick(t)
                move_tick(t)
                cast_tick(t)
                look_tick(t)
        finally:
            release_keys()
            release_use()
            release_attack()
            restore_slot()
            say("STOPPED")

main()