from __future__ import annotations

import os
from dataclasses import dataclass, field
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


def _custom_forward_source_commands() -> dict[str, str]:
    out: dict[str, str] = {}
    for pair in _csv("FORWARD_SOURCE_COMMANDS"):
        if ":" not in pair:
            continue
        source, command = pair.split(":", 1)
        source, command = source.strip().lower(), command.strip().lower()
        if source and command:
            out[source] = command if command.startswith("/") else f"/{command}"
    return out


@dataclass(frozen=True)
class Settings:
    bot_token: str = os.getenv("BOT_TOKEN", "").strip()
    mongo_uri: str = os.getenv("MONGO_URI", "").strip()
    db_name: str = os.getenv("DB_NAME", "bika_adding_lookup").strip() or "bika_adding_lookup"
    owner_ids: tuple[int, ...] = tuple(
        int(x) for x in _csv("OWNER_IDS") if x.strip().lstrip("-").isdigit()
    )
    adding_chat_id: int = _int("ADDING_CHAT_ID", 0)

    run_mode: str = os.getenv("RUN_MODE", "auto").strip().lower()
    public_url: str = os.getenv("PUBLIC_URL", "").rstrip("/")
    webhook_path: str = os.getenv("WEBHOOK_PATH", "/webhook").strip() or "/webhook"
    webhook_secret: str = os.getenv("WEBHOOK_SECRET", "").strip()
    port: int = _int("PORT", 10000)
    host: str = os.getenv("HOST", "0.0.0.0").strip() or "0.0.0.0"

    log_level: str = os.getenv("LOG_LEVEL", "INFO").upper()
    default_command: str = os.getenv("DEFAULT_COMMAND", "/hallow").strip() or "/hallow"
    default_source_key: str = os.getenv(
        "DEFAULT_SOURCE_KEY", "items_characters_hallow"
    ).strip() or "items_characters_hallow"
    owner_username: str = os.getenv("OWNER_USERNAME", "@Official_Bika").strip()
    added_log_channel: str = os.getenv("ADDED_LOG_CHANNEL", "").strip()
    forward_source_commands: dict[str, str] = field(
        default_factory=_custom_forward_source_commands
    )

    bot_api_base_url: str = os.getenv("BOT_API_BASE_URL", "").strip().rstrip("/")
    bot_api_is_local: bool = _bool("BOT_API_IS_LOCAL", False)
    bot_api_session_limit: int = max(32, min(500, _int("BOT_API_SESSION_LIMIT", 100)))

    mongo_server_selection_timeout_ms: int = _int(
        "MONGO_SERVER_SELECTION_TIMEOUT_MS", 2500
    )
    mongo_connect_timeout_ms: int = _int("MONGO_CONNECT_TIMEOUT_MS", 2500)
    mongo_socket_timeout_ms: int = _int("MONGO_SOCKET_TIMEOUT_MS", 8000)
    mongo_min_pool_size: int = _int("MONGO_MIN_POOL_SIZE", 2)
    mongo_max_pool_size: int = _int("MONGO_MAX_POOL_SIZE", 24)
    mongo_max_idle_time_ms: int = _int("MONGO_MAX_IDLE_TIME_MS", 120000)

    source_channels: tuple[str, ...] = field(
        default_factory=lambda: tuple(_csv("SOURCE_CHANNELS"))
    )
    helper_forward_delay: int = max(1, _int("HELPER_FORWARD_DELAY", 1))
    helper_max_history: int = max(1, _int("HELPER_MAX_HISTORY", 500))
    helper_inline_timeout: int = max(1, _int("HELPER_INLINE_TIMEOUT", 20))


settings = Settings()
