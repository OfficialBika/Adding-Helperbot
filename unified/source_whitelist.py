from __future__ import annotations

from typing import Any

from unified.config import settings


def _norm(value: Any) -> str:
    return str(value or "").strip().lower().lstrip("@").replace(" ", "")


def _configured_sources() -> tuple[str, ...]:
    import os
    return tuple(
        item.strip()
        for item in os.getenv("SOURCE_CHANNELS", "").split(",")
        if item.strip()
    )


def _chat_values(chat: Any) -> set[str]:
    if chat is None:
        return set()

    values: set[str] = set()
    chat_id = getattr(chat, "id", None)
    if chat_id is not None:
        values.add(str(chat_id).strip())

    username = getattr(chat, "username", None)
    if username:
        values.add(_norm(username))

    title = getattr(chat, "title", None)
    if title:
        values.add(_norm(title))

    return values


def forwarded_origin_chat(message: Any):
    origin = getattr(message, "forward_origin", None)
    if origin is not None:
        return getattr(origin, "chat", None) or getattr(origin, "sender_chat", None)
    return getattr(message, "forward_from_chat", None)


def is_allowed_source(message: Any) -> bool:
    """Authorize ingestion from Telegram forward metadata only.

    Content/caption parsing is never used as authorization. A source must be
    explicitly present in SOURCE_CHANNELS by numeric chat ID or username.
    """
    configured = _configured_sources()
    if not configured:
        return False

    allowed = {_norm(x) for x in configured}
    origin_chat = forwarded_origin_chat(message)
    if origin_chat is None:
        return False

    values = _chat_values(origin_chat)
    return bool(values & allowed)


def allowed_source_label(message: Any) -> str | None:
    origin_chat = forwarded_origin_chat(message)
    if origin_chat is None:
        return None
    username = getattr(origin_chat, "username", None)
    if username:
        return "@" + str(username).lstrip("@")
    chat_id = getattr(origin_chat, "id", None)
    return str(chat_id) if chat_id is not None else getattr(origin_chat, "title", None)
