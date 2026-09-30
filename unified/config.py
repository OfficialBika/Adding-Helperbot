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

    # One and only one chat is allowed to create database records.
    adding_chat_id: int = _int("ADDING_CHAT_ID", 0)

    auto_lookup_enabled: bool = _bool("AUTO_LOOKUP_ENABLED", True)
    lookup_in_private: bool = _bool("LOOKUP_IN_PRIVATE", True)
    lookup_in_groups: bool = _bool("LOOKUP_IN_GROUPS", True)
    reply_not_found: bool = _bool("LOOKUP_REPLY_NOT_FOUND", True)
    # Enable exact Telegram file_unique_id recovery when forwarded media has no source scope.
    v3_global_exact_fallback: bool = _bool("V3_GLOBAL_EXACT_FALLBACK", True)

    run_mode: str = os.getenv("RUN_MODE", "auto").strip().lower()
    public_url: str = os.getenv("PUBLIC_URL", "").rstrip("/")
    webhook_path: str = os.getenv("WEBHOOK_PATH", "/webhook")
    webhook_secret: str = os.getenv("WEBHOOK_SECRET", "")
    port: int = _int("PORT", 10000)
    host: str = os.getenv("HOST", "0.0.0.0")

    log_level: str = os.getenv("LOG_LEVEL", "INFO").upper()
    photo_threshold: int = _int("PHOTO_PHASH_THRESHOLD", 8)
    dhash_threshold: int = _int("PHOTO_DHASH_THRESHOLD", 12)
    video_frame_threshold: int = _int("VIDEO_FRAME_THRESHOLD", 10)
    video_avg_threshold: int = _int("VIDEO_AVG_THRESHOLD", 12)
    max_photo_candidates: int = _int("MAX_PHOTO_CANDIDATES", 1200)
    max_video_candidates: int = _int("MAX_VIDEO_CANDIDATES", 1500)
    # LookupV4 local exact-UID acceleration.
    lookup_sqlite_path: str = os.getenv("LOOKUP_SQLITE_PATH", "data/lookup_index.sqlite3").strip() or "data/lookup_index.sqlite3"
    lookup_ram_cache_max_items: int = _int("LOOKUP_RAM_CACHE_MAX_ITEMS", 5000)
    lookup_index_sync_seconds: int = _int("LOOKUP_INDEX_SYNC_SECONDS", 300)

    # Auto lookup uses a fast exact-UID phase first. Hash fallback can run
    # asynchronously so a slow Telegram media download never blocks webhook
    # acknowledgement for the normal lookup path.
    auto_hash_lookup_enabled: bool = _bool("AUTO_HASH_LOOKUP_ENABLED", True)
    auto_hash_timeout_seconds: int = max(
        5, _int("AUTO_HASH_TIMEOUT_SECONDS", 10)
    )

    # Optional Force Join / membership verification gate for user lookups.
    # Syntax: @public_channel|https://t.me/public_channel,@another|https://t.me/another
    # Private/numeric chats must provide an explicit join URL.
    force_join_enabled: bool = _bool("FORCE_JOIN_ENABLED", False)
    force_join_channels: str = os.getenv("FORCE_JOIN_CHANNELS", "").strip()
    force_join_cache_ttl_seconds: int = _int("FORCE_JOIN_CACHE_TTL_SECONDS", 60)
    force_join_cache_max_users: int = _int("FORCE_JOIN_CACHE_MAX_USERS", 10000)
    force_join_bypass_authorized: bool = _bool("FORCE_JOIN_BYPASS_AUTHORIZED", True)


settings = Settings()
