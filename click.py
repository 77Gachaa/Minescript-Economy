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
MOVE_EPS           = 0.01    # position change bigger than this = "moved" -> stop
RESUME_DELAY       = 1.0
LEFT_CLICK_ENABLES = True    # a real left click turns auto-click back on

# Alarms
ALARM_ACTION       = "disconnect"   # "disconnect" = leave the server, "beep" = old beeping alarm
MOVE_ALARM         = True    # position changed -> alarm (also stops clicking)
MSG_ALARM          = True    # someone sends you a /msg -> alarm
NO_STAND_ALARM     = True    # not looking at an armor stand for too long -> alarm
NO_STAND_SECONDS   = 2.0     # seconds without an armor stand before the alarm
                             # (the timer does not run during an AFK check)
PLAYER_ALARM       = True    # another player comes within PLAYER_RANGE -> alarm
PLAYER_RANGE       = 20      # blocks
PLAYER_CHECK       = 0.5     # how often to look for players (seconds)
HOTBAR_ALARM       = True    # hotbar items added / removed / moved / count changed -> alarm
HOTBAR_IGNORE_ADDED = ["armadillo_scute"]   # these may be ADDED without an alarm
                                            # (moving or removing them still alarms)
HOTBAR_CHECK       = 0.25    # how often to compare the hotbar (seconds)
PLAYER_WHITELIST   = ["Westl1fe", "LexQiqi", "Ivaniam", "Svea", "014K"]   # case-insensitive

# Target check
ONLY_ARMOR_STAND   = True
TARGET_RANGE       = 6       # how far to look for the target (blocks)

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

# Enchant routine (runs when XP level >= XP_LEVEL_TRIGGER)
XP_ROUTINE        = True
XP_LEVEL_TRIGGER  = 200
XP_CHECK          = 1.0      # how often to check your level (seconds)
XP_COOLDOWN       = 0      # wait this long after a routine before it can run again
XP_MAX_SECONDS    = 600      # abort the whole routine after this long
CE_COMMAND        = "/ce"
CE_KEYWORDS       = ["elite", "ultimate"]   # buttons to click (matched in item name/lore)
CE_FAIL_PHRASES   = ["not enough", "can't afford", "cannot afford",
                     "don't have enough", "insufficient", "need more"]

# --- buying speed (tune these) ---
CE_BURST          = 5        # clicks sent per tick on one button. Higher = faster, 1 = old behaviour
CE_BURST_PAUSE_MIN = 0.2    # pause between bursts (seconds). Lower = faster
CE_BURST_PAUSE_MAX = 0.21
CE_MAX_CLICKS     = 1500     # safety cap on total buy clicks per routine
CE_NOCHANGE_LIMIT = 5        # bursts that change nothing before a button counts as unaffordable
CE_OPEN_DELAY     = 0.15     # wait after /ce GUI appears before the first click

# --- vault / storing speed ---
PV_COMMAND        = "/pv 5"
STORE_KEYWORDS    = ["elite", "ultimate"]   # inventory items to shift-click into the vault
STORE_BURST       = 4        # stacks shift-clicked per scan
STORE_DELAY       = 0.08     # pause between store bursts
STORE_TRIES       = 3        # give up on a stack after this many failed shift-clicks
PV_LOAD_DELAY     = 0.35     # wait after the vault opens so its contents load
PV_CMD_DELAY      = 0.25     # wait after closing /ce before sending /pv
GUI_WAIT          = 4.0      # how long to wait for a GUI to open

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
DUMP_KEY   = 299   # F10 list the open GUI's items (use to tune the keywords)
XP_NOW_KEY = 301   # F12 run the enchant routine right now (testing)
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
ac_was_blocked = True
no_stand_since = None

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

# enchant routine state
xp_state = "idle"            # idle, ce_wait, ce_click, pv_cmd, pv_wait, store
xp_t = 0.0
xp_deadline = 0.0
xp_started = 0.0
xp_next_check = 0.0
xp_cooldown_until = 0.0
xp_clicks = 0
xp_idx = 0
xp_dead = set()
xp_nochange = {}
xp_last_slot = None
xp_last_snap = None
xp_fail_flag = False
xp_stored = 0
xp_tries = {}

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
CE_FAIL = [norm(p) for p in CE_FAIL_PHRASES]

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
    if ALARM_ACTION == "disconnect" and allow_disconnect:
        say("ALARM: " + reason + " -> disconnecting")
        if disconnect_now(reason):
            return
        say("Disconnect failed, using the beep alarm instead")
    alarm_on = True
    try:
        minescript.echo_json({
            "text": TAG + " ALARM: " + reason + "  (press P to silence)",
            "color": "red"})
    except Exception:
        say("ALARM: " + reason + "  (press P to silence)")
    threading.Thread(target=alarm_loop, daemon=True).start()

# ── GUI clicking ──────────────────────────────────────────────────────────────
def click_many(slots, mode_name="PICKUP"):
    # Click each slot in `slots` once, in order. Looks up the Java objects ONCE
    # and remembers which click method works, so bursts are cheap.
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

# ── Target check (armor stand under the crosshair) ───────────────────────────
def _is_stand(text):
    text = str(text).lower()
    return "armor_stand" in text or "armor stand" in text

def target_seen():
    # Returns (is_armor_stand, description). Checks two independent ways.
    desc = []

    # 1) Minescript's own raycast
    try:
        ent = minescript.player_get_targeted_entity(TARGET_RANGE)
        if ent is None:
            desc.append("minescript=none")
        else:
            info = str(ent.type) + " " + str(ent.name)
            desc.append("minescript=" + info)
            if _is_stand(info):
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
            if _is_stand(info):
                return True, " | ".join(desc)
    except Exception as e:
        desc.append("game=err(" + str(e)[:40] + ")")

    return False, " | ".join(desc)

def looking_at_armor_stand():
    if not ONLY_ARMOR_STAND:
        return True
    ok, desc = target_seen()
    if not ok:
        status("not looking at an armor stand (" + desc + ")")
    return ok

# ── Auto-click ────────────────────────────────────────────────────────────────
def autoclick_blocked(t):
    if alarm_on:
        status("alarm is on (P to silence)")
        return True
    if xp_state != "idle":
        status("enchant routine running")
        return True
    if paused:
        status("paused (F7 to resume)")
        return True
    if afk_active:
        status("AFK check in progress")
        return True
    if t < afk_hold_until:
        status("AFK check announced, waiting")
        return True
    s = minescript.screen_name()
    if s is not None:
        status("a screen is open: " + str(s))
        return True
    return False

def autoclick_tick(t):
    global ac_next_t, ac_release_t, ac_base, ac_was_blocked, auto_click_on, no_stand_since

    if ac_release_t and t >= ac_release_t:
        release_attack()

    if not auto_click_on:
        no_stand_since = None
        status("auto-click is OFF (F6 or left click to turn on)")
        return

    if autoclick_blocked(t):
        no_stand_since = None            # no countdown during AFK check / pause / screens
        if ac_release_t:
            release_attack()
        ac_was_blocked = True
        return

    if not ensure_sword(t):
        no_stand_since = None
        status("no sword in hand / switching")
        if ac_release_t:
            release_attack()
        ac_was_blocked = True
        return

    pos = tuple(minescript.player_position())

    if ac_was_blocked or ac_base is None:
        ac_base = pos
        ac_was_blocked = False
        no_stand_since = None
        ac_next_t = t + RESUME_DELAY
        status("anchored, starting in " + str(RESUME_DELAY) + "s")
        return

    if any(abs(c - s) > MOVE_EPS for c, s in zip(pos, ac_base)):
        release_attack()
        auto_click_on = False
        no_stand_since = None
        msg = ("Position changed from " + str([round(c, 2) for c in ac_base]) +
               " to " + str([round(c, 2) for c in pos]))
        say(msg + " - auto-click stopped (F6 or left click to turn it back on)")
        if MOVE_ALARM:
            trigger_alarm(msg)
        return

    # armor stand check + "no armor stand for N seconds" alarm
    if looking_at_armor_stand():
        no_stand_since = None
    else:
        if no_stand_since is None:
            no_stand_since = t
        elif NO_STAND_ALARM and t - no_stand_since >= NO_STAND_SECONDS:
            no_stand_since = None
            trigger_alarm("No armor stand for " + str(NO_STAND_SECONDS) + "s")
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
    # only watch while running; re-baseline after pause / screens / auto-click off / enchant routine
    if (not HOTBAR_ALARM or paused or not auto_click_on or afk_active
            or xp_state != "idle" or minescript.screen_name() is not None):
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
    if alarm_on or paused or afk_active or t < afk_hold_until or xp_state != "idle":
        return
    if t < next_feed_t:
        return
    try:
        minescript.execute(FEED_COMMAND)
        say("Sent " + FEED_COMMAND)
    except Exception as e:
        say("Can't send " + FEED_COMMAND + ": " + str(e))
    next_feed_t = t + FEED_EVERY

# ── Enchant routine: /ce -> buy until broke -> /pv 5 -> store ─────────────────
def container_items():
    try:
        return minescript.container_get_items() or []
    except Exception:
        return []

def item_text(i):
    return (str(i.item) + " " + str(i.nbt or "")).lower()

def container_size():
    # slots in the top container = all menu slots minus the 36 player inventory slots
    try:
        return int(Minecraft.getInstance().player.containerMenu.slots.size()) - 36
    except Exception:
        items = container_items()
        return (max(i.slot for i in items) + 1 - 36) if items else 0

def find_slots(words, min_slot=0, max_slot=None):
    out = []
    for i in container_items():
        if i.slot is None or i.slot < min_slot:
            continue
        if max_slot is not None and i.slot >= max_slot:
            continue
        txt = item_text(i)
        if any(w in txt for w in words):
            out.append(i.slot)
    return out

def find_ce():
    size = container_size()
    return find_slots(CE_KEYWORDS, 0, size if size > 0 else None)

def close_gui():
    try:
        Minecraft.getInstance().player.closeContainer()
    except Exception:
        try:
            Minecraft.getInstance().setScreen(None)
        except Exception as e:
            say("Can't close GUI: " + str(e))

def xp_level():
    try:
        return int(Minecraft.getInstance().player.experienceLevel)
    except Exception:
        return None

def xp_snapshot():
    try:
        p = Minecraft.getInstance().player
        return (int(p.experienceLevel), round(float(p.experienceProgress), 3), int(p.totalExperience))
    except Exception:
        return None

def dump_container():
    items = container_items()
    size = container_size()
    say("GUI dump: top container = slots 0-" + str(size - 1) + ", " + str(len(items)) + " items total")
    for i in items:
        txt = item_text(i)
        match = any(w in txt for w in set(CE_KEYWORDS + STORE_KEYWORDS))
        if i.slot < size or match:
            say("slot " + str(i.slot) + ("*" if match else "") + ": " + str(i.item) +
                " x" + str(i.count) + " | " + str(i.nbt or "")[:100])

def xp_begin(t):
    global xp_state, xp_deadline, xp_started, xp_clicks, xp_idx, xp_dead, xp_nochange
    global xp_last_slot, xp_last_snap, xp_fail_flag, xp_stored, xp_tries
    release_attack()
    xp_clicks = 0
    xp_idx = 0
    xp_dead = set()
    xp_nochange = {}
    xp_last_slot = None
    xp_last_snap = None
    xp_fail_flag = False
    xp_stored = 0
    xp_tries = {}
    xp_started = t
    say("Level " + str(xp_level()) + ": starting enchant routine")
    minescript.execute(CE_COMMAND)
    xp_state = "ce_wait"
    xp_deadline = t + GUI_WAIT

def xp_finish(t, why):
    global xp_state, xp_cooldown_until, hotbar_base, ac_was_blocked
    if gui_is_open():
        close_gui()
    xp_state = "idle"
    xp_cooldown_until = t + XP_COOLDOWN
    hotbar_base = None          # hotbar legitimately changed, so re-baseline (no alarm)
    ac_was_blocked = True       # re-anchor position before auto-click resumes
    say("Routine finished: " + why + " (" + str(xp_clicks) + " buy clicks, " +
        str(xp_stored) + " stacks stored)")

def xp_tick(t):
    global xp_state, xp_t, xp_deadline, xp_next_check, xp_clicks, xp_idx
    global xp_last_slot, xp_last_snap, xp_fail_flag, xp_stored

    if xp_state == "idle":
        if (not XP_ROUTINE or alarm_on or paused or not auto_click_on or afk_active
                or t < afk_hold_until or t < xp_cooldown_until or t < xp_next_check
                or minescript.screen_name() is not None):
            return
        xp_next_check = t + XP_CHECK
        lvl = xp_level()
        if lvl is not None and lvl >= XP_LEVEL_TRIGGER:
            xp_begin(t)
        return

    if alarm_on or paused:
        xp_finish(t, "aborted (alarm / pause)")
        return
    if afk_active or t < afk_hold_until:
        xp_deadline = max(xp_deadline, t + GUI_WAIT)    # wait out an AFK check
        return
    if t - xp_started > XP_MAX_SECONDS:
        xp_finish(t, "took too long")
        return

    if xp_state == "ce_wait":
        if gui_is_open() and find_ce():
            xp_state = "ce_click"
            xp_t = t + CE_OPEN_DELAY
        elif t > xp_deadline:
            xp_finish(t, "/ce GUI didn't open or no item matched " + str(CE_KEYWORDS) +
                      " (open it and press F10 to check)")
        return

    if xp_state == "ce_click":
        if not gui_is_open():
            xp_state = "pv_cmd"
            xp_t = t + PV_CMD_DELAY
            return
        if t < xp_t:
            return
        snap = xp_snapshot()
        if xp_last_slot is not None:          # judge the previous burst
            if xp_fail_flag:
                xp_dead.add(xp_last_slot)
                say("Slot " + str(xp_last_slot) + ": can't afford")
            elif snap == xp_last_snap:
                xp_nochange[xp_last_slot] = xp_nochange.get(xp_last_slot, 0) + 1
                if xp_nochange[xp_last_slot] >= CE_NOCHANGE_LIMIT:
                    xp_dead.add(xp_last_slot)
                    say("Slot " + str(xp_last_slot) + ": XP not changing, treating as unaffordable")
            else:
                xp_nochange[xp_last_slot] = 0
        xp_fail_flag = False
        alive = [s for s in find_ce() if s not in xp_dead]
        if not alive or xp_clicks >= CE_MAX_CLICKS:
            say("Done buying, closing GUI")
            close_gui()
            xp_state = "pv_cmd"
            xp_t = t + PV_CMD_DELAY
            return
        slot = alive[xp_idx % len(alive)]
        xp_idx += 1
        done = click_many([slot] * CE_BURST, "PICKUP")     # burst of clicks on one button
        if done == 0:
            xp_finish(t, "click failed")
            return
        xp_last_slot = slot
        xp_last_snap = snap
        xp_clicks += done
        xp_t = t + random.uniform(CE_BURST_PAUSE_MIN, CE_BURST_PAUSE_MAX)
        return

    if xp_state == "pv_cmd":
        if t < xp_t:
            return
        if gui_is_open():
            close_gui()
            xp_t = t + PV_CMD_DELAY
            return
        minescript.execute(PV_COMMAND)
        xp_state = "pv_wait"
        xp_deadline = t + GUI_WAIT
        return

    if xp_state == "pv_wait":
        if gui_is_open():
            xp_state = "store"
            xp_t = t + PV_LOAD_DELAY      # let the vault contents load
        elif t > xp_deadline:
            xp_finish(t, "/pv GUI didn't open")
        return

    if xp_state == "store":
        if not gui_is_open():
            xp_finish(t, "vault GUI closed")
            return
        if t < xp_t:
            return
        size = container_size()
        if size <= 0:
            xp_finish(t, "can't tell the vault size")
            return
        all_left = find_slots(STORE_KEYWORDS, size)
        slots = [s for s in all_left if xp_tries.get(s, 0) < STORE_TRIES]
        if not slots:
            if all_left:
                say("Vault may be full: " + str(len(all_left)) + " stack(s) not moved")
            xp_finish(t, "storing done")
            return
        batch = slots[:STORE_BURST]
        for s in batch:
            xp_tries[s] = xp_tries.get(s, 0) + 1
        done = click_many(batch, "QUICK_MOVE")     # shift-click several stacks per scan
        if done == 0:
            xp_finish(t, "shift-click failed")
            return
        xp_stored += done
        xp_t = t + STORE_DELAY + random.uniform(0, 0.03)
        return

# ── Event handlers ────────────────────────────────────────────────────────────
def on_chat(message):
    global afk_hold_until, last_chat_norm, last_chat_t, xp_fail_flag
    message = str(message)
    if message.startswith(TAG):
        return
    low = norm(message)
    now = time.time()
    if low == last_chat_norm and now - last_chat_t < 1.5:
        return
    last_chat_norm = low
    last_chat_t = now

    if xp_state == "ce_click" and any(p in low for p in CE_FAIL):
        xp_fail_flag = True

    if any(p in low for p in NAFK):
        afk_hold_until = time.time() + AFK_HOLD_SECONDS
        release_attack()
        say("AFK check announced, auto-click paused")
        return

    if MSG_ALARM and not paused and auto_click_on:
        m = MSG_RE.search(message)
        if m:
            trigger_alarm("MSG from " + m.group(1).strip())

def on_key(event):
    global stopped, paused, alarm_on, auto_click_on, ac_was_blocked, auto_feed_on, next_feed_t
    global no_stand_since
    if event.action != 1:
        return
    if DEBUG:
        say("(dbg) key code " + str(event.key))
    if event.key == STOP_KEY:
        stopped = True
        alarm_on = False
        return
    if event.key == DUMP_KEY:
        if gui_is_open():
            dump_container()
        return
    if event.key == ALARM_OFF_KEY:
        # only when no screen is open, so typing "p" in chat doesn't trigger it
        if alarm_on and minescript.screen_name() is None:
            alarm_on = False
            ac_was_blocked = True
            no_stand_since = None
            say("Alarm silenced" +
                ("" if auto_click_on else " - auto-click is still OFF (F6 or left click)"))
        return
    if alarm_on and event.key in (TOGGLE_KEY, CLICK_KEY) and minescript.screen_name() is None:
        alarm_on = False                 # pausing / switching off also silences the alarm
        no_stand_since = None
    if minescript.screen_name() is not None or alarm_on:
        return
    if event.key == TOGGLE_KEY:
        paused = not paused
        if paused:
            release_attack()
        say("PAUSED" if paused else "RUNNING")
    elif event.key == FEED_KEY:
        auto_feed_on = not auto_feed_on
        if auto_feed_on:
            next_feed_t = time.time() + FEED_EVERY
        say("Auto-feed " + ("ON" if auto_feed_on else "OFF"))
    elif event.key == CLICK_KEY:
        auto_click_on = not auto_click_on
        ac_was_blocked = True
        if not auto_click_on:
            release_attack()
        say("Auto-click " + ("ON" if auto_click_on else "OFF"))
    elif event.key == XP_NOW_KEY:
        if xp_state == "idle":
            xp_begin(time.time())

def on_mouse(event):
    global auto_click_on, ac_was_blocked
    if not LEFT_CLICK_ENABLES:
        return
    if event.button != 0 or event.action != 1:   # left button, press only
        return
    if auto_click_on or alarm_on:
        return
    if minescript.screen_name() is not None:     # ignore clicks inside menus/chat
        return
    auto_click_on = True
    ac_was_blocked = True                        # re-anchor to the current position
    say("Auto-click ON (left click)")

# ── Main loop ─────────────────────────────────────────────────────────────────
def main():
    global next_feed_t
    say("Loaded. " + ("PAUSED - press F7. " if paused else "") +
        "F6 auto-click, F7 pause, F8 auto-feed, P silence alarm, F9 stop, F10 GUI dump, "
        "F12 run enchant routine, left click re-enables. Auto-click " +
        ("ON" if auto_click_on else "OFF") + ", auto-feed " + ("ON" if auto_feed_on else "OFF") +
        " (" + FEED_COMMAND + " every " + str(FEED_EVERY) + "s). Alarm action: " + ALARM_ACTION +
        ". Enchant routine " + ("at level " + str(XP_LEVEL_TRIGGER) if XP_ROUTINE else "OFF"))
    if ClickEnum is None:
        say("WARNING: click class not found; GUI clicking will fail (alarm will sound).")

    sslot = find_sword_slot()
    say("Check: sword slot " + ("NONE FOUND in hotbar" if sslot is None else str(sslot)))

    next_feed_t = time.time() + (0 if FEED_ON_START else FEED_EVERY)

    log_open()
    with minescript.EventQueue() as events:
        events.register_chat_listener()
        events.register_key_listener()
        events.register_mouse_listener()
        events.register_world_listener()
        try:
            while not stopped:
                # while buying / storing, don't sit waiting on the event queue
                fast = xp_state in ("ce_click", "store")
                try:
                    if fast:
                        ev = events.get(block=False)
                    else:
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
                xp_tick(t)
                autoclick_tick(t)
                if fast:
                    time.sleep(0.002)      # avoid pegging a CPU core while waiting between bursts
        finally:
            release_attack()
            say("STOPPED")

main()