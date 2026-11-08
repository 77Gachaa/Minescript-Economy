r"""
book_disenchant.py

Loops until the chest has no enchanted books left:
  1. Smooth-turn toward the chest (yaw only, pitch stays the same as when you
     started), open it, shift-click enchanted books into your inventory (only
     as many as you have free slots).
  2. Smooth-turn back to the yaw/pitch you had when you started the script,
     open the grindstone, and for every enchanted book: shift-click it in,
     then shift-click the output out -> plain book.
  3. Repeat. Stops when a chest visit finds no enchanted books, when your
     inventory has no free slot, or when you open the chat.

The grindstone must be under your crosshair at the starting yaw/pitch.
Needs rotation.py in the same minescript folder.

Usage:  \book_disenchant
Stop :  open chat (T or /), or  \jobs  then  \killjob JOB_ID
"""
import math
import time
import random
import minescript as ms
from java import JavaClass
from rotation import look, get_axes


def first_class(*names):
    for n in names:
        try:
            return JavaClass(n)
        except Exception:
            pass
    return None


# Newer Minecraft renamed ClickType -> ContainerInput; try both.
ClickEnum = first_class(
    "net.minecraft.world.inventory.ContainerInput",
    "net.minecraft.world.inventory.ClickType",
)

# ---------------- CONFIG ----------------
# X/Z of the chest. For a double chest, use the LEFT half:
# block (100, 200) -> (100.5, 200.5)
# Only the yaw (left/right turn) is taken from this; pitch stays as it was.
CHEST_AIM_X = 100.5
CHEST_AIM_Z = 200.5

BOOK_NAME = "enchanted_book"
GRINDSTONE_OUTPUT_SLOT = 2     # grindstone menu: 0,1 = inputs, 2 = output, 3-38 = player inv
GRINDSTONE_SIZE = 3
SCREEN_TIMEOUT = 5.0
MAX_ROUNDS = 100               # safety cap on loop iterations

# --- speed (seconds). Lower = faster. Raise them if the server lags/kicks. ---
CLICK_DELAY = (0.005, 0.02)    # random pause between chest shift-clicks
SYNC_DELAY = 0.12              # wait after a GUI opens so its items sync
OUTPUT_TIMEOUT = 0.6           # max wait for the grindstone output to appear
GRIND_CLICK_DELAY = (0.0, 0.01)  # pause after taking the output, before the next book
CLOSE_DELAY = 0.05             # pause after closing a GUI
# ----------------------------------------


class ChatOpened(Exception):
    pass


def check_chat():
    """Stop the whole script as soon as the chat screen is open."""
    name = ms.screen_name()
    if name and "chat" in name.lower():
        raise ChatOpened()


def sleep(sec):
    """time.sleep that notices the chat being opened."""
    end = time.time() + sec
    while True:
        check_chat()
        left = end - time.time()
        if left <= 0:
            return
        time.sleep(min(0.05, left))


def rsleep(rng):
    lo, hi = rng
    d = lo + random.random() * (hi - lo)
    if d > 0:
        sleep(d)
    else:
        check_chat()


def mc_instance():
    return JavaClass("net.minecraft.client.Minecraft").getInstance()


def wait_for_screen(timeout=SCREEN_TIMEOUT):
    end = time.time() + timeout
    while time.time() < end:
        check_chat()
        if ms.screen_name():
            sleep(SYNC_DELAY)  # let the contents sync from the server
            return True
        time.sleep(0.01)
    return False


def wait_for_no_screen(timeout=SCREEN_TIMEOUT):
    end = time.time() + timeout
    while time.time() < end:
        check_chat()
        if not ms.screen_name():
            return True
        time.sleep(0.01)
    return False


def close_screen():
    mc_instance().player.closeContainer()
    wait_for_no_screen()
    sleep(CLOSE_DELAY)


def right_click():
    ms.player_press_use(True)
    time.sleep(0.04)
    ms.player_press_use(False)


def shift_click(mc, menu, slot):
    """Shift-click (QUICK_MOVE) a menu slot. Tries new and old method names."""
    check_chat()
    last = None
    for method in ("handleContainerInput", "handleInventoryMouseClick"):
        try:
            getattr(mc.gameMode, method)(
                menu.containerId, slot, 0, ClickEnum.QUICK_MOVE, mc.player)
            return True
        except Exception as e:
            last = e
    ms.echo("Shift-click failed: " + str(last))
    return False


def free_slots():
    used = {s.slot for s in ms.player_inventory() if 0 <= s.slot < 36}
    return 36 - len(used)


def book_slots(lo, hi):
    """Menu slot indexes in [lo, hi) that hold an enchanted book."""
    items = ms.container_get_items() or []
    return sorted(s.slot for s in items if lo <= s.slot < hi and BOOK_NAME in s.item)


def wait_output(menu):
    """Poll until the grindstone output slot has an item (no fixed delay)."""
    end = time.time() + OUTPUT_TIMEOUT
    while time.time() < end:
        check_chat()
        try:
            if menu.getSlot(GRINDSTONE_OUTPUT_SLOT).hasItem():
                return True
        except Exception:
            sleep(0.12)  # can't read the slot, fall back to a fixed wait
            return True
        time.sleep(0.005)
    return False


def take_books_from_chest(limit):
    mc = mc_instance()
    menu = mc.player.containerMenu
    chest_size = menu.slots.size() - 36
    if chest_size <= 0:
        ms.echo("Chest didn't open as a container.")
        return 0

    slots = book_slots(0, chest_size)
    ms.echo(f"Chest has {len(slots)} enchanted books, taking up to {limit}.")
    taken = 0
    for slot in slots[:limit]:
        if not shift_click(mc, menu, slot):
            break
        taken += 1
        rsleep(CLICK_DELAY)
    sleep(0.05)
    return taken


def disenchant_books():
    mc = mc_instance()
    menu = mc.player.containerMenu
    if menu.slots.size() - 36 != GRINDSTONE_SIZE:
        ms.echo("That doesn't look like a grindstone. Aim the starting yaw/pitch at it.")
        return 0

    # Snapshot, so a cursed book that stays enchanted can't loop forever.
    slots = book_slots(GRINDSTONE_SIZE, menu.slots.size())
    ms.echo(f"Disenchanting {len(slots)} books...")
    done = 0
    for slot in slots:
        if not shift_click(mc, menu, slot):      # book -> grindstone input
            break
        if not wait_output(menu):
            ms.echo(f"No output for slot {slot}, skipping.")
            continue
        if not shift_click(mc, menu, GRINDSTONE_OUTPUT_SLOT):  # plain book -> inventory
            break
        done += 1
        rsleep(GRIND_CLICK_DELAY)
    return done


def run():
    if ClickEnum is None:
        ms.echo("Click enum class not found, can't move items.")
        return

    # The chat you typed the command in may still be closing, wait for it.
    wait_for_no_screen(1.5)
    sleep(0.2)

    start_yaw, start_pitch = ms.player_orientation()
    feet_y = math.floor(ms.player().position[1])
    # Yaw toward the chest only; pitch stays what it was at the start.
    chest_yaw = get_axes(CHEST_AIM_X, feet_y + 0.5, CHEST_AIM_Z)[0]

    total_taken = 0
    total_done = 0
    for rnd in range(1, MAX_ROUNDS + 1):
        check_chat()
        space = free_slots()
        if space <= 0:
            ms.echo("Inventory has no free slot, stopping.")
            break

        # --- chest ---
        look(chest_yaw, start_pitch)
        sleep(0.05)
        right_click()
        if not wait_for_screen():
            ms.echo("Chest screen never opened.")
            break
        taken = take_books_from_chest(space)
        close_screen()
        if taken == 0:
            ms.echo("No enchanted books left in the chest.")
            look(start_yaw, start_pitch)
            break
        total_taken += taken

        # --- back to the grindstone ---
        look(start_yaw, start_pitch)
        sleep(0.05)
        right_click()
        if not wait_for_screen():
            ms.echo("Grindstone screen never opened.")
            break
        done = disenchant_books()
        total_done += done
        sleep(0.05)
        close_screen()
        ms.echo(f"Round {rnd}: took {taken}, disenchanted {done}.")

    ms.echo(f"Finished. Took {total_taken} books, disenchanted {total_done}.")


def main():
    try:
        run()
    except ChatOpened:
        ms.player_press_use(False)
        ms.echo("Chat opened, script stopped.")


main()