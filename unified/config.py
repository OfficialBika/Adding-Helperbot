from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path

from dotenv import load_dotenv

_ENV_FILE = Path(__file__).resolve().parents[1] / ".env"
load_dotenv(dotenv_path=_ENV_FILE, override=True)


def _bool(name: str, default: bool = False) -> bool:
    return os.getenv(name, str(default)).strip().lower() in {"1", "true", "yes", "on", "y"}


def _int(name: str, default: int = 0) -> int:
    try:
        return int(os.getenv(name, str(default)).strip())
    except Exception:
        return default


def _csv(name: str) -> list[str]:
    return [x.strip() for x in os.getenv(name, "").split(",") if x.strip()]


def _csv_ints(name: str) -> tuple[int, ...]:
    values: list[int] = []
    for item in _csv(name):
        try:
            values.append(int(item))
        except (TypeError, ValueError):
            continue
    return tuple(values)


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
    # Positive exact-UID cache: only successful lookups are cached.
    lookup_uid_cache_max_items: int = _int("LOOKUP_UID_CACHE_MAX_ITEMS", 300000)
    lookup_uid_cache_ttl_seconds: int = _int("LOOKUP_UID_CACHE_TTL_SECONDS", 3600)
    # Local SQLite exact-UID accelerator. MongoDB remains the source of truth.
    uid_index_path: str = os.getenv("UID_INDEX_PATH", "data/uid_index.sqlite3").strip() or "data/uid_index.sqlite3"
    uid_index_backfill_batch: int = max(100, min(5000, _int("UID_INDEX_BACKFILL_BATCH", 1000)))

    # Force Join is opt-in. Legacy single-channel variables remain supported.
    force_join_enabled: bool = _bool("FORCE_JOIN_ENABLED", False)
    force_join_chat_id: int = _int("FORCE_JOIN_CHAT_ID", 0)
    force_join_url: str = os.getenv("FORCE_JOIN_URL", "").strip()
    force_join_title: str = os.getenv("FORCE_JOIN_TITLE", "").strip()
    force_join_button_text: str = os.getenv("FORCE_JOIN_BUTTON_TEXT", "Join Channel").strip() or "Join Channel"
    # Positive membership is cached longer; negative membership stays short.
    # The explicit verification callback always bypasses both TTLs.
    force_join_positive_cache_seconds: int = max(60, _int("FORCE_JOIN_POSITIVE_CACHE_SECONDS", 21600))
    force_join_negative_cache_seconds: int = max(1, _int("FORCE_JOIN_NEGATIVE_CACHE_SECONDS", 15))

    # Multi-channel Force Join. IDs, URLs and titles are matched by position.
    force_join_chat_ids: tuple[int, ...] = _csv_ints("FORCE_JOIN_CHAT_IDS")
    force_join_urls: tuple[str, ...] = tuple(_csv("FORCE_JOIN_URLS"))
    force_join_titles: tuple[str, ...] = tuple(_csv("FORCE_JOIN_TITLES"))

    def __post_init__(self) -> None:
        if self.force_join_chat_ids:
            expected = len(self.force_join_chat_ids)
            if len(self.force_join_urls) != expected:
                raise ValueError(f"FORCE_JOIN_URLS count must match FORCE_JOIN_CHAT_IDS count ({len(self.force_join_urls)} != {expected})")
            if any(not str(url).strip() for url in self.force_join_urls):
                raise ValueError("FORCE_JOIN_URLS entries must be non-empty when FORCE_JOIN_CHAT_IDS is configured")
            if self.force_join_titles and len(self.force_join_titles) != expected:
                raise ValueError(f"FORCE_JOIN_TITLES count must be either 0 or match FORCE_JOIN_CHAT_IDS count ({len(self.force_join_titles)} != {expected})")

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

    # Optional self-hosted Telegram Bot API. Disabled by default so existing
    # deployments continue using api.telegram.org unchanged.
    bot_api_base_url: str = os.getenv("BOT_API_BASE_URL", "").strip().rstrip("/")
    bot_api_is_local: bool = _bool("BOT_API_IS_LOCAL", False)
    bot_api_session_limit: int = max(32, min(500, _int("BOT_API_SESSION_LIMIT", 100)))
    # VPS/Mongo latency tuning; all values remain environment-configurable.
    mongo_server_selection_timeout_ms: int = _int("MONGO_SERVER_SELECTION_TIMEOUT_MS", 2500)
    mongo_connect_timeout_ms: int = _int("MONGO_CONNECT_TIMEOUT_MS", 2500)
    mongo_socket_timeout_ms: int = _int("MONGO_SOCKET_TIMEOUT_MS", 8000)
    mongo_min_pool_size: int = _int("MONGO_MIN_POOL_SIZE", 2)
    mongo_max_pool_size: int = _int("MONGO_MAX_POOL_SIZE", 24)
    mongo_max_idle_time_ms: int = _int("MONGO_MAX_IDLE_TIME_MS", 120000)


settings = Settings()
