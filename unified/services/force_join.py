from __future__ import annotations

import asyncio
import logging
import time
from collections import OrderedDict

from aiogram import F, Router
from aiogram.types import CallbackQuery, InlineKeyboardButton, InlineKeyboardMarkup, Message

from unified.config import settings
from unified.store import db

router = Router(name="unified_force_join")
log = logging.getLogger("unified.force_join")

# Membership cache. Positive membership is stable enough to cache for hours;
# negative membership is deliberately short so newly joined users pass quickly.
# The explicit verification callback clears the user entries before checking.
_POSITIVE_CACHE_TTL = float(settings.force_join_positive_cache_seconds)
_NEGATIVE_CACHE_TTL = float(settings.force_join_negative_cache_seconds)
_CACHE_MAX = 20_000
_membership_cache: "OrderedDict[tuple[int, int], tuple[float, bool]]" = OrderedDict()
_cache_lock = asyncio.Lock()

# Prompt throttling is scoped by chat + user so a group prompt never suppresses
# the DM verification screen opened immediately afterwards.
_prompt_cache: "OrderedDict[tuple[int, int], float]" = OrderedDict()
_PROMPT_TTL = 30.0

# Bot username is stable for the lifetime of the process and is used to build
# a Telegram deep-link from groups into the bot's private chat.
_bot_username: str = ""
_bot_username_lock = asyncio.Lock()


def _channels() -> tuple[tuple[int, str, str], ...]:
    """Return (chat_id, url, title) in configured order.

    Multi-channel settings take precedence when FORCE_JOIN_CHAT_IDS is set.
    Legacy single-channel settings remain fully supported for existing deploys.
    """
    multi_ids = tuple(settings.force_join_chat_ids)
    multi_urls = tuple(settings.force_join_urls)
    multi_titles = tuple(settings.force_join_titles)

    if multi_ids:
        channels: list[tuple[int, str, str]] = []
        for index, chat_id in enumerate(multi_ids):
            url = multi_urls[index] if index < len(multi_urls) else ""
            title = (
                multi_titles[index]
                if index < len(multi_titles)
                else f"Channel {index + 1}"
            )
            channels.append((int(chat_id), url, title))
        return tuple(channels)

    if settings.force_join_chat_id:
        return (
            (
                int(settings.force_join_chat_id),
                settings.force_join_url,
                settings.force_join_title or "the required channel",
            ),
        )

    return ()


async def _enabled() -> bool:
    """Resolve runtime Force Join state, falling back to environment config."""
    if not _channels():
        return False
    try:
        doc = await db.settings.find_one({"key": "force_join:enabled"})
        if doc is not None:
            return bool(doc.get("enabled", False))
    except Exception:
        log.exception("FORCE_JOIN runtime state read failed; using env default")
    return bool(settings.force_join_enabled)


async def _get_bot_username(bot) -> str:
    global _bot_username
    if _bot_username:
        return _bot_username

    async with _bot_username_lock:
        if _bot_username:
            return _bot_username
        try:
            me = await bot.get_me()
            _bot_username = str(getattr(me, "username", "") or "").lstrip("@")
        except Exception:
            log.exception("FORCE_JOIN failed to resolve bot username for DM deep-link")
        return _bot_username


def _remember(key: tuple[int, int], value: bool) -> None:
    _membership_cache.pop(key, None)
    _membership_cache[key] = (time.monotonic(), value)
    while len(_membership_cache) > _CACHE_MAX:
        _membership_cache.popitem(last=False)


async def _cached_member(bot, chat_id: int, user_id: int) -> bool | None:
    key = (int(chat_id), int(user_id))
    async with _cache_lock:
        item = _membership_cache.get(key)
        if item:
            age = time.monotonic() - item[0]
            ttl = _POSITIVE_CACHE_TTL if item[1] else _NEGATIVE_CACHE_TTL
            if age <= ttl:
                _membership_cache.move_to_end(key)
                return item[1]
            _membership_cache.pop(key, None)

    try:
        member = await bot.get_chat_member(int(chat_id), int(user_id))
    except Exception as exc:
        # Fail closed while Force Join is enabled: an API failure must not
        # silently bypass a required channel. Log the exact channel so a
        # misconfigured ID/admin permission can be diagnosed from server logs.
        log.warning(
            "FORCE_JOIN membership check failed chat_id=%s user_id=%s error=%s: %s",
            chat_id,
            user_id,
            type(exc).__name__,
            exc,
        )
        return None

    status = str(getattr(member, "status", "") or "").lower()
    joined = status in {"creator", "administrator", "member"} or (
        status == "restricted" and bool(getattr(member, "is_member", False))
    )

    async with _cache_lock:
        _remember(key, joined)
    return joined


async def _check_all_channels(bot, user_id: int) -> tuple[bool, bool]:
    """Return (all_joined, verification_error).

    Every configured channel is checked. A single missing membership blocks
    access; an API error never counts as joined.
    """
    verification_error = False

    results = await asyncio.gather(
        *(
            _cached_member(bot, chat_id, user_id)
            for chat_id, _, _ in _channels()
        ),
        return_exceptions=True,
    )

    for (chat_id, _, _), result in zip(_channels(), results):
        if isinstance(result, Exception) or result is None:
            verification_error = True
            log.warning(
                "FORCE_JOIN verification unavailable chat_id=%s user_id=%s",
                chat_id,
                user_id,
            )
        elif result is False:
            log.info(
                "FORCE_JOIN user not joined chat_id=%s user_id=%s",
                chat_id,
                user_id,
            )
            return False, verification_error

    return not verification_error, verification_error


def _keyboard(include_dm_button: bool = False) -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    channels = _channels()

    for index, (_, url, title) in enumerate(channels, start=1):
        if url:
            # Preserve the old custom button label for legacy single-channel
            # configuration; multi-channel buttons use their channel titles.
            if not settings.force_join_chat_ids and len(channels) == 1:
                button_text = settings.force_join_button_text
            else:
                button_text = title or f"Channel {index}"
            rows.append([InlineKeyboardButton(text=f"📢 {button_text}", url=url)])

    if include_dm_button:
        # The URL is filled by _prompt because the bot username is only known
        # through Telegram's getMe API.
        pass
    else:
        rows.append(
            [
                InlineKeyboardButton(
                    text="✅ I Joined — Check Again",
                    callback_data="fj:check",
                )
            ]
        )

    return InlineKeyboardMarkup(inline_keyboard=rows)


def _text() -> str:
    channels = _channels()
    if len(channels) == 1:
        required = f"<b>{channels[0][2]}</b>"
    else:
        lines = [
            f"• <b>{title or f'Channel {index}'}</b>"
            for index, (_, _, title) in enumerate(channels, start=1)
        ]
        required = "\n".join(lines)

    return (
        "🔒 <b>Join Required</b>\n\n"
        "Please join <b>all required channels</b> before using character lookup.\n\n"
        f"{required}\n\n"
        "After joining all channels, tap <b>✅ I Joined — Check Again</b>."
    )


def _dm_text() -> str:
    return (
        "🔐 <b>Verification Required</b>\n\n"
        "Please join all required channels below, then tap "
        "<b>✅ I Joined — Check Again</b>."
    )


async def _prompt(message: Message, unavailable: bool = False) -> None:
    user = getattr(message, "from_user", None)
    if not user:
        return

    user_id = int(user.id)
    chat_id = int(getattr(getattr(message, "chat", None), "id", 0) or 0)
    cache_key = (chat_id, user_id)
    now = time.monotonic()

    async with _cache_lock:
        last = _prompt_cache.get(cache_key, 0.0)
        if now - last < _PROMPT_TTL:
            return
        _prompt_cache.pop(cache_key, None)
        _prompt_cache[cache_key] = now
        while len(_prompt_cache) > _CACHE_MAX:
            _prompt_cache.popitem(last=False)

    # In groups, keep the verification flow private: the user gets one button
    # that opens this bot in DM. The actual channel buttons + re-check button
    # are shown only inside the private chat.
    if getattr(getattr(message, "chat", None), "type", None) != "private":
        username = await _get_bot_username(message.bot)
        if not username:
            log.error("FORCE_JOIN cannot create DM deep-link: bot username unavailable")
            text = (
                "🔒 <b>Join Required</b>\n\n"
                "Please open this bot in private chat to verify your membership."
            )
            await message.reply(text, disable_web_page_preview=True)
            return

        text = (
            "🔒 <b>Join Required</b>\n\n"
            "Please open the bot in private chat to complete channel verification."
        )
        keyboard = InlineKeyboardMarkup(
            inline_keyboard=[
                [
                    InlineKeyboardButton(
                        text="🔐 Verify in Bot DM",
                        url=f"https://t.me/{username}?start=forcejoin",
                    )
                ]
            ]
        )
        await message.reply(
            text,
            reply_markup=keyboard,
            disable_web_page_preview=True,
        )
        return

    if unavailable:
        text = (
            "⚠️ <b>Membership check unavailable.</b>\n\n"
            "Telegram membership verification failed. Please tap "
            "<b>✅ I Joined — Check Again</b> to retry."
        )
    else:
        text = _dm_text()

    await message.reply(
        text,
        reply_markup=_keyboard(),
        disable_web_page_preview=True,
    )


async def set_force_join_enabled(enabled: bool) -> bool:
    """Persist runtime Force Join state and clear verification caches."""
    await db.settings.update_one(
        {"key": "force_join:enabled"},
        {
            "$set": {
                "key": "force_join:enabled",
                "enabled": bool(enabled),
                "updated_at": __import__("datetime").datetime.now(__import__("datetime").timezone.utc),
            }
        },
        upsert=True,
    )
    async with _cache_lock:
        _membership_cache.clear()
        _prompt_cache.clear()
    return bool(enabled)


async def force_join_status() -> bool:
    return await _enabled()


async def send_dm_verification(message: Message) -> None:
    """Show the private Force Join verification screen."""
    if not await _enabled():
        await message.reply("ℹ️ Force Join is currently disabled.")
        return

    await _prompt(message)


async def require_join(message: Message) -> bool:
    if not await _enabled():
        return True

    user = getattr(message, "from_user", None)
    if not user:
        return False

    # Owners are never blocked by the operational access gate.
    if int(user.id) in settings.owner_ids:
        return True

    joined, verification_error = await _check_all_channels(
        message.bot,
        int(user.id),
    )

    if joined:
        return True

    await _prompt(message, unavailable=verification_error)
    return False


@router.callback_query(F.data == "fj:check")
async def force_join_check(callback: CallbackQuery):
    user = getattr(callback, "from_user", None)
    if not user:
        await callback.answer()
        return

    if not _enabled():
        await callback.answer("Force Join is disabled.", show_alert=False)
        return

    # Explicit re-check must bypass every cached membership result.
    user_id = int(user.id)
    async with _cache_lock:
        for chat_id, _, _ in _channels():
            _membership_cache.pop((int(chat_id), user_id), None)

    joined, verification_error = await _check_all_channels(
        callback.bot,
        user_id,
    )

    if joined:
        await callback.answer("✅ All required channels confirmed.", show_alert=False)
        if callback.message:
            try:
                await callback.message.edit_text(
                    "✅ <b>Verified.</b> You can use character lookup now."
                )
            except Exception:
                pass
        return

    if verification_error:
        await callback.answer(
            "⚠️ Could not verify all channels right now. Please try again.",
            show_alert=True,
        )
        return

    await callback.answer(
        "❌ Please join all required channels first.",
        show_alert=True,
    )


__all__ = ["router", "require_join", "send_dm_verification", "set_force_join_enabled", "force_join_status"]
