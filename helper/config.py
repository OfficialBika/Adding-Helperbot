import os

API_ID = int(os.getenv("API_ID", "0") or 0)
API_HASH = os.getenv("API_HASH", "")
SESSION_STRING = os.getenv("SESSION_STRING", "")
TARGET_CHAT = os.getenv("HELPER_TARGET_CHAT", "")

SOURCES = {
    "catch": {"bot": os.getenv("CATCH_BOT", "@CharacterCatcherBot"), "command": "/check"},
    "grab": {"bot": os.getenv("GRAB_BOT", "@GrabGardenBot"), "command": "/check"},
    "senpai": {"bot": os.getenv("SENPAI_BOT", "@SenpaiCatcher"), "command": "/see"},
    "hallow": {"bot": os.getenv("HALLOW_BOT", "@CharacterHallowBot"), "command": "/show"},
    "takers": {"bot": os.getenv("TAKERS_BOT", "@TakersBot"), "command": "/detect"},
}
