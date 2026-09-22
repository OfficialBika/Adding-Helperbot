from __future__ import annotations

import os

from dotenv import load_dotenv

load_dotenv(override=True)


def _csv(name: str) -> list[str]:
    return [x.strip() for x in os.getenv(name, "").split(",") if x.strip()]


def _int(name: str, default: int = 0) -> int:
    try:
        return int(os.getenv(name, str(default)).strip())
    except Exception:
        return default


API_ID = _int("API_ID")
API_HASH = os.getenv("API_HASH", "").strip()
SESSION_STRING = os.getenv("SESSION_STRING", "").strip()

# The helper is a userbot account. It may only forward from these explicitly
# configured source chats. It never sends commands/DMs to source bots.
ADDING_CHAT_ID = _int("ADDING_CHAT_ID")
INLINE_OUTPUT_CHAT_ID = _int("INLINE_OUTPUT_CHAT_ID", ADDING_CHAT_ID)

SOURCE_CHATS = tuple(_csv("SOURCE_CHANNELS"))
OWNER_IDS = frozenset(_int(x, 0) for x in _csv("OWNER_IDS") if x.isdigit())

HELPER_FORWARD_DELAY = max(0.5, float(os.getenv("HELPER_FORWARD_DELAY", "1.0")))
HELPER_MAX_HISTORY = max(1, min(5000, _int("HELPER_MAX_HISTORY", 500)))
HELPER_INLINE_TIMEOUT = max(5, min(60, _int("HELPER_INLINE_TIMEOUT", 20)))
