import os

API_ID = int(os.getenv("API_ID", "0") or 0)
API_HASH = os.getenv("API_HASH", "")
SESSION_STRING = os.getenv("SESSION_STRING", "")

TARGET_CHAT = os.getenv("HELPER_TARGET_CHAT", "")


# Helper crawler source registry
# Kept in config so controller can import it safely.
# Values can be overridden later from environment/runtime.

from types import SimpleNamespace

SOURCES = {
    "character_catcher": SimpleNamespace(
        key="character_catcher",
        bot=os.getenv("CATCH_BOT", "@CharacterCatchBot"),
        command="/check",
    ),
    "senpai_catcher": SimpleNamespace(
        key="senpai_catcher",
        bot=os.getenv("SENPAI_BOT", "@SenpaiCatcher"),
        command="/see",
    ),
    "characters_hallow": SimpleNamespace(
        key="characters_hallow",
        bot=os.getenv("HALLOW_BOT", "@CharacterHallowBot"),
        command="/show",
    ),
    "takers_character": SimpleNamespace(
        key="takers_character",
        bot=os.getenv("TAKERS_BOT", "@TakersBot"),
        command="/detect",
    ),
    "waifux_grab": SimpleNamespace(
        key="waifux_grab",
        bot=os.getenv("GRAB_BOT", "@GrabGarden"),
        command="/check",
    ),
}
