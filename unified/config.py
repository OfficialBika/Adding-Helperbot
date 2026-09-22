from __future__ import annotations

import os
from dataclasses import dataclass

from dotenv import load_dotenv

load_dotenv(override=True)

def _bool(name: str, default: bool = False) -> bool:
    return os.getenv(name, str(default)).strip().lower() in {"1", "true", "yes", "on", "y"}

def _int(name: str, default: int = 0) -> int:
    try:
        return int(os.getenv(name, str(default)).strip())
    except Exception:
        return default

def _csv(name: str) -> list[str]:
    return [x.strip() for x in os.getenv(name, "").split(",") if x.strip()]

@dataclass(frozen=True)
class Settings:
    bot_token: str = os.getenv("BOT_TOKEN", "").strip()
    mongo_uri: str = os.getenv("MONGO_URI", "").strip()
    db_name: str = os.getenv("DB_NAME", "bika_adding_lookup").strip() or "bika_adding_lookup"
    owner_ids: tuple[int, ...] = tuple(int(x) for x in _csv("OWNER_IDS") if x.isdigit())

    adding_chat_id: int = _int("ADDING_CHAT_ID", 0)
    auto_lookup_enabled: bool = _bool("AUTO_LOOKUP_ENABLED", True)
    lookup_in_private: bool = _bool("LOOKUP_IN_PRIVATE", True)
    lookup_in_groups: bool = _bool("LOOKUP_IN_GROUPS", True)
    reply_not_found: bool = _bool("LOOKUP_REPLY_NOT_FOUND", True)

    # auto: webhook when PUBLIC_URL exists, otherwise polling.
    # polling/webhook: explicit deployment mode.
    run_mode: str = os.getenv("RUN_MODE", "auto").strip().lower()
    public_url: str = os.getenv("PUBLIC_URL", "").rstrip("/")
    webhook_path: str = os.getenv("WEBHOOK_PATH", "/webhook")
    webhook_secret: str = os.getenv("WEBHOOK_SECRET", "")
    port: int = _int("PORT", 10000)
    host: str = os.getenv("HOST", "0.0.0.0")

    api_id: int = _int("API_ID", 0)
    api_hash: str = os.getenv("API_HASH", "")
    session_string: str = os.getenv("SESSION_STRING", "")
    helper_target_chat: str = os.getenv("HELPER_TARGET_CHAT", "")

    log_level: str = os.getenv("LOG_LEVEL", "INFO").upper()
    photo_threshold: int = _int("PHOTO_PHASH_THRESHOLD", 8)
    dhash_threshold: int = _int("PHOTO_DHASH_THRESHOLD", 12)
    video_frame_threshold: int = _int("VIDEO_FRAME_THRESHOLD", 10)
    video_avg_threshold: int = _int("VIDEO_AVG_THRESHOLD", 12)
    max_photo_candidates: int = _int("MAX_PHOTO_CANDIDATES", 1200)
    max_video_candidates: int = _int("MAX_VIDEO_CANDIDATES", 1500)

settings = Settings()
