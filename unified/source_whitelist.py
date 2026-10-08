from __future__ import annotations

from typing import Any

from unified.config import settings
from helper.registry import match_config
from unified.source_resolver import BOT_SOURCE_COLLECTION, BOT_SOURCE_USER_ID, BOT_SOURCE_CHAT_ID


def _norm(value: Any) -> str:
    return str(value or "").strip().lower().lstrip("@").replace(" ", "")


def forwarded_origin_chat(message: Any):
    origin = getattr(message, "forward_origin", None)
    if origin is not None:
        return getattr(origin, "chat", None) or getattr(origin, "sender_chat", None)
    return getattr(message, "forward_from_chat", None)


def _chat_values(chat: Any) -> set[str]:
    if chat is None:
        return set()
    values: set[str] = set()
    if getattr(chat, "id", None) is not None:
        values.add(str(chat.id).strip())
    if getattr(chat, "username", None):
        values.add(_norm(chat.username))
    if getattr(chat, "title", None):
        values.add(_norm(chat.title))
    return values


def _user_values(user: Any) -> set[str]:
    if user is None:
        return set()
    values: set[str] = set()
    if getattr(user, "id", None) is not None:
        values.add(str(user.id).strip())
    if getattr(user, "username", None):
        values.add(_norm(user.username))
    return values


def _forwarded_source_user(message: Any):
    origin = getattr(message, "forward_origin", None)
    if origin is not None and getattr(origin, "sender_user", None) is not None:
        return origin.sender_user
    return getattr(message, "forward_from", None)


def is_allowed_source(message: Any) -> bool:
    configured = {_norm(x) for x in settings.source_channels}
    origin_chat = forwarded_origin_chat(message)

    dynamic = match_config(
        username=getattr(origin_chat, "username", None) if origin_chat else None,
        chat_id=getattr(origin_chat, "id", None) if origin_chat else None,
        title=getattr(origin_chat, "title", None) if origin_chat else None,
        forward=True,
    )
    if dynamic:
        return True

    if origin_chat is not None and _chat_values(origin_chat) & configured:
        return True

    if origin_chat is not None:
        origin_values = _chat_values(origin_chat)
        if origin_values & {str(x) for x in BOT_SOURCE_CHAT_ID}:
            return True
        if origin_values & {_norm(x) for x in BOT_SOURCE_COLLECTION}:
            return True

    for user in (
        _forwarded_source_user(message),
        getattr(message, "via_bot", None),
        getattr(message, "from_user", None) if getattr(getattr(message, "from_user", None), "is_bot", False) else None,
    ):
        if user is None:
            continue
        values = _user_values(user)
        if any(v.isdigit() and int(v) in BOT_SOURCE_USER_ID for v in values):
            return True
        if values & {_norm(x) for x in BOT_SOURCE_COLLECTION}:
            return True

    return False
