from __future__ import annotations

from typing import Any

from unified.config import settings
from config import BOT_SOURCE_COLLECTION, BOT_SOURCE_USER_ID


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


def _user_values(user: Any) -> set[str]:
    if user is None:
        return set()

    values: set[str] = set()
    user_id = getattr(user, "id", None)
    if user_id is not None:
        values.add(str(user_id).strip())

    username = getattr(user, "username", None)
    if username:
        values.add(_norm(username))

    return values


def _forwarded_source_user(message: Any):
    origin = getattr(message, "forward_origin", None)
    if origin is not None:
        sender_user = getattr(origin, "sender_user", None)
        if sender_user is not None:
            return sender_user

    # Legacy Bot API forward metadata.
    return getattr(message, "forward_from", None)


def is_allowed_source(message: Any) -> bool:
    """Authorize ingestion from explicit Telegram forward/source metadata.

    Chat forwards are checked against SOURCE_CHANNELS. Directly forwarded bot
    messages (for example Helper forwarding @SenpaiCatcherBot responses) do not
    have a forward-origin chat, so they are checked against the explicit
    BOT_SOURCE_* maps as well. Content/caption text is never used as
    authorization.
    """
    configured = _configured_sources()
    allowed = {_norm(x) for x in configured}

    origin_chat = forwarded_origin_chat(message)
    if origin_chat is not None:
        values = _chat_values(origin_chat)
        if values & allowed:
            return True

    source_user = _forwarded_source_user(message)
    user_values = _user_values(source_user)
    if user_values & allowed:
        return True

    # Bot-user forwards such as @SenpaiCatcherBot are not represented as a
    # chat in MessageOriginUser. Treat only the explicitly configured source
    # identities in BOT_SOURCE_* as authorized; never infer from caption text.
    for value in user_values:
        if value.isdigit():
            try:
                if int(value) in BOT_SOURCE_USER_ID:
                    return True
            except Exception:
                pass
        username = "@" + value.lstrip("@") if value and not value.isdigit() else None
        if username and username in BOT_SOURCE_COLLECTION:
            return True

    return False


def allowed_source_label(message: Any) -> str | None:
    origin_chat = forwarded_origin_chat(message)
    if origin_chat is None:
        return None
    username = getattr(origin_chat, "username", None)
    if username:
        return "@" + str(username).lstrip("@")
    chat_id = getattr(origin_chat, "id", None)
    return str(chat_id) if chat_id is not None else getattr(origin_chat, "title", None)
