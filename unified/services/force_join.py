from __future__ import annotations

import asyncio
import time
from collections import OrderedDict

from aiogram import F, Router
from aiogram.types import CallbackQuery, InlineKeyboardButton, InlineKeyboardMarkup, Message

from unified.config import settings

router = Router(name="unified_force_join")

# Short positive/negative membership cache. This avoids a Telegram API call on
# every lookup while still reacting quickly when a user joins.
_CACHE_TTL = 60.0
_CACHE_MAX = 20_000
_membership_cache: "OrderedDict[tuple[int, int], tuple[float, bool]]" = OrderedDict()
_cache_lock = asyncio.Lock()
_prompt_cache: "OrderedDict[int, float]" = OrderedDict()
_PROMPT_TTL = 30.0


def _enabled() -> bool:
    return bool(settings.force_join_enabled and settings.force_join_chat_id)


def _remember(key: tuple[int, int], value: bool) -> None:
    _membership_cache.pop(key, None)
    _membership_cache[key] = (time.monotonic(), value)
    while len(_membership_cache) > _CACHE_MAX:
        _membership_cache.popitem(last=False)


async def _cached_member(bot, user_id: int) -> bool | None:
    key = (int(settings.force_join_chat_id), int(user_id))
    async with _cache_lock:
        item = _membership_cache.get(key)
        if item:
            age = time.monotonic() - item[0]
            if age <= _CACHE_TTL:
                _membership_cache.move_to_end(key)
                return item[1]
            _membership_cache.pop(key, None)

    try:
        member = await bot.get_chat_member(settings.force_join_chat_id, int(user_id))
    except Exception:
        # A broken/missing channel configuration must not turn lookup into a
        # global outage. The feature is therefore fail-open on API errors.
        return None

    status = str(getattr(member, "status", "") or "").lower()
    joined = status in {"creator", "administrator", "member"} or (
        status == "restricted" and bool(getattr(member, "is_member", False))
    )
    async with _cache_lock:
        _remember(key, joined)
    return joined


def _keyboard() -> InlineKeyboardMarkup:
    rows = []
    if settings.force_join_url:
        rows.append([InlineKeyboardButton(text=settings.force_join_button_text, url=settings.force_join_url)])
    rows.append([InlineKeyboardButton(text="✅ I Joined — Check Again", callback_data="fj:check")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _text() -> str:
    channel = settings.force_join_title or "the required channel"
    return (
        "🔒 <b>Join Required</b>\n\n"
        f"Please join <b>{channel}</b> before using character lookup.\n\n"
        "After joining, tap <b>✅ I Joined — Check Again</b>."
    )


async def require_join(message: Message) -> bool:
    if not _enabled():
        return True

    user = getattr(message, "from_user", None)
    if not user:
        return False

    # Owners are never blocked by an operational access gate.
    if int(user.id) in settings.owner_ids:
        return True

    joined = await _cached_member(message.bot, int(user.id))
    if joined is True:
        return True

    # API/config errors are fail-open; only an explicit non-member result blocks.
    if joined is None:
        return True

    now = time.monotonic()
    async with _cache_lock:
        last = _prompt_cache.get(int(user.id), 0.0)
        if now - last < _PROMPT_TTL:
            return False
        _prompt_cache.pop(int(user.id), None)
        _prompt_cache[int(user.id)] = now
        while len(_prompt_cache) > _CACHE_MAX:
            _prompt_cache.popitem(last=False)

    await message.reply(_text(), reply_markup=_keyboard(), disable_web_page_preview=True)
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

    # Do not trust the cached negative result after the user explicitly asks
    # for a re-check. Remove it first and query Telegram again.
    key = (int(settings.force_join_chat_id), int(user.id))
    async with _cache_lock:
        _membership_cache.pop(key, None)

    joined = await _cached_member(callback.bot, int(user.id))
    if joined is True:
        await callback.answer("✅ Membership confirmed.", show_alert=False)
        if callback.message:
            try:
                await callback.message.edit_text("✅ <b>Verified.</b> You can use character lookup now.")
            except Exception:
                pass
        return

    if joined is None:
        await callback.answer("⚠️ Could not verify right now. Please try again.", show_alert=True)
        return

    await callback.answer("❌ You have not joined yet.", show_alert=True)


__all__ = ["router", "require_join"]
