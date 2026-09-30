from __future__ import annotations

import asyncio
import logging
import sys
import time
from pathlib import Path

try:
    import resource
except ImportError:  # pragma: no cover
    resource = None

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "namebotv3"))
sys.path.insert(0, str(ROOT))

from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command
from aiogram.types import Message
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application

from unified.config import settings
from unified.store import characters, close, ensure_indexes
from unified.auth import ensure_auth_indexes, is_authorized, grant, revoke, list_authorized
from unified.ingest import ingest_message
from unified.lookup import lookup_message
from unified.lookup_index import lookup_index
from unified.force_join import force_join
from helper.runtime import HelperUserbot
from helper.manager import HelperManager
from services.result_formatter import result_buttons
from services.source_resolver import resolve_source_collection
from utils.text import h, first_token

logging.basicConfig(
    level=getattr(logging, settings.log_level, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
log = logging.getLogger("unified")
PROCESS_STARTED_AT = time.monotonic()


def _uptime_text() -> str:
    seconds = max(0, int(time.monotonic() - PROCESS_STARTED_AT))
    days, seconds = divmod(seconds, 86400)
    hours, seconds = divmod(seconds, 3600)
    minutes, seconds = divmod(seconds, 60)
    if days:
        return f"{days}d {hours}h {minutes}m"
    if hours:
        return f"{hours}h {minutes}m {seconds}s"
    if minutes:
        return f"{minutes}m {seconds}s"
    return f"{seconds}s"


def _process_rss_mb() -> float:
    if resource is None:
        return 0.0
    try:
        return float(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss) / 1024.0
    except Exception:
        return 0.0


async def _ping_db_ms() -> float | None:
    try:
        started = time.perf_counter()
        await characters.database.command("ping")
        return (time.perf_counter() - started) * 1000.0
    except Exception:
        return None


async def _ping_bot_ms(message: Message) -> float | None:
    try:
        started = time.perf_counter()
        await message.bot.get_me()
        return (time.perf_counter() - started) * 1000.0
    except Exception:
        return None


def _ms_text(value: float | None) -> str:
    return "N/A" if value is None else f"{value:.0f} ms"


router = Router(name="unified")
helper_userbot = HelperUserbot()
helper_manager = HelperManager(helper_userbot)


def owner(message: Message) -> bool:
    return bool(message.from_user and message.from_user.id in settings.owner_ids)


async def has_admin_access(message: Message) -> bool:
    user = getattr(message, "from_user", None)
    if not user:
        return False
    return owner(message) or await is_authorized(user.id)


def is_media(message: Message) -> bool:
    return bool(
        getattr(message, "photo", None)
        or getattr(message, "video", None)
        or getattr(message, "animation", None)
        or getattr(message, "document", None)
    )

async def enforce_lookup_access(message: Message) -> bool:
    """Require channel membership for human-initiated lookups.

    Bot-to-bot/source messages and channel-originated messages have no human
    actor to verify, so they are intentionally not blocked by Force Join.
    Owners always bypass. Authorized helper users can bypass when configured.
    """
    user = getattr(message, "from_user", None)
    if not user or bool(getattr(user, "is_bot", False)):
        return True

    user_id = getattr(user, "id", None)
    if not user_id:
        return True

    if owner(message):
        return True

    if settings.force_join_bypass_authorized and await is_authorized(int(user_id)):
        return True

    result = await force_join.verify(message.bot, int(user_id))
    if result.verified:
        return True

    if result.error:
        await message.reply(
            "⚠️ <b>Verification temporarily unavailable.</b>\n\n"
            "Please try the <b>✅ Verify</b> button again shortly.",
            reply_markup=force_join.keyboard(),
            disable_web_page_preview=True,
        )
        return False

    await message.reply(
        force_join.prompt(),
        reply_markup=force_join.keyboard(),
        disable_web_page_preview=True,
    )
    return False



def is_ingest_candidate(message: Message) -> bool:
    """Allow media plus source-bot/helper text-only metadata replies."""
    if is_media(message):
        return True
    text = str(
        getattr(message, "text", None)
        or getattr(message, "caption", None)
        or ""
    )
    if not text.strip():
        return False
    from_user = getattr(message, "from_user", None)
    helper_id = helper_userbot.user_id
    if helper_id and getattr(from_user, "id", None) == helper_id:
        return True
    if getattr(from_user, "is_bot", False) and resolve_source_collection(message):
        return True
    lowered = text.lower()
    return (
        "character valuation" in lowered
        or "character with id" in lowered and "not found" in lowered
    )


def format_ingest_notice(result: dict) -> str:
    status = str(result.get("status") or "").lower()
    doc = result.get("document") or {}
    name = h(str(doc.get("name") or "Unknown"))
    character_id = h(str(doc.get("character_id") or "—"))
    source = h(str(doc.get("source_key") or "unknown"))
    command = h(str(doc.get("command") or "/name"))
    media_type = h(str(doc.get("media_type") or "unknown"))

    if status == "unchanged":
        return "This media have been saved."

    if status == "saved":
        return (
            "✅ <b>CHARACTER SAVED</b>\n\n"
            f"Name: <code>{name}</code>\n"
            f"ID: <code>{character_id}</code>\n"
            f"Command: <code>{command}</code>\n"
            f"Source: <code>{source}</code>\n"
            f"Media: <code>{media_type}</code>\n"
            "Status: <code>NEW</code>"
        )

    if status == "updated":
        changes = list(result.get("changes") or [])
        lines = []
        for change in changes[:12]:
            lines.append(f"• {h(str(change))}")
        if len(changes) > 12:
            lines.append(f"• ...and {len(changes) - 12} more")
        details = "\n".join(lines) if lines else "• record fields changed"
        return (
            "🔄 <b>CHARACTER UPDATED</b>\n\n"
            f"Name: <code>{name}</code>\n"
            f"ID: <code>{character_id}</code>\n"
            f"Source: <code>{source}</code>\n"
            f"Media: <code>{media_type}</code>\n\n"
            "<b>Updated:</b>\n"
            f"{details}"
        )

    return ""

def format_result(doc: dict) -> str:
    name = h(str(doc.get("name") or ""))
    command = str(doc.get("command") or "/name")
    hint = h(f"{command} {first_token(str(doc.get('name') or ''))}")
    full = h(f"{command} {str(doc.get('name') or '')}")
    return (
        f"<b>NAME :</b> <code>{name}</code>\n"
        "────────────────\n"
        f"🔹 <b>Hint :</b> <code>{hint}</code>\n"
        f"🔸 <b>Full :</b> <code>{full}</code>\n\n"
        "Powered by <b>Bika</b>"
    )


@router.callback_query(F.data == "forcejoin:verify")
async def forcejoin_verify(callback_query):
    user = getattr(callback_query, "from_user", None)
    if not user:
        await callback_query.answer("Unable to identify the user.", show_alert=True)
        return

    user_id = int(user.id)
    callback_message = getattr(callback_query, "message", None)
    if callback_message is not None and owner(callback_message):
        verified = True
        error = ""
    elif settings.force_join_bypass_authorized and await is_authorized(user_id):
        verified = True
        error = ""
    else:
        result = await force_join.verify(callback_query.bot, user_id)
        verified = result.verified
        error = result.error

    if verified:
        await callback_query.answer("✅ Verified successfully.", show_alert=False)
        message = getattr(callback_query, "message", None)
        if message:
            try:
                await message.edit_text(force_join.success_text(), reply_markup=None)
            except Exception:
                pass
        return

    if error:
        await callback_query.answer("Verification is temporarily unavailable.", show_alert=True)
    else:
        await callback_query.answer("Please join all required channels first.", show_alert=True)

    message = getattr(callback_query, "message", None)
    if message:
        try:
            await message.edit_text(
                force_join.prompt(),
                reply_markup=force_join.keyboard(),
            )
        except Exception:
            pass


@router.message(Command("verify"))
async def forcejoin_verify_command(message: Message):
    user = getattr(message, "from_user", None)
    if not user or bool(getattr(user, "is_bot", False)):
        return

    if owner(message) or (
        settings.force_join_bypass_authorized
        and await is_authorized(int(user.id))
    ):
        await message.reply(force_join.success_text())
        return

    result = await force_join.verify(message.bot, int(user.id))
    if result.verified:
        await message.reply(force_join.success_text())
    elif result.error:
        await message.reply(
            "⚠️ <b>Verification temporarily unavailable.</b>\n\n"
            "Please try again shortly.",
            reply_markup=force_join.keyboard(),
        )
    else:
        await message.reply(
            force_join.prompt(),
            reply_markup=force_join.keyboard(),
            disable_web_page_preview=True,
        )


@router.message(Command("auth"))
async def auth_user(message: Message):
    if not owner(message):
        return
    target = getattr(message, "reply_to_message", None)
    user_id = getattr(getattr(target, "from_user", None), "id", None) if target else None
    if user_id is None:
        parts = (message.text or "").strip().split()
        if len(parts) >= 2:
            raw = parts[1].strip()
            if raw.startswith("@"):
                try:
                    chat = await message.bot.get_chat(raw)
                    user_id = getattr(chat, "id", None)
                except Exception:
                    user_id = None
            elif raw.lstrip("-").isdigit():
                user_id = int(raw)
    if not user_id:
        await message.reply("Usage: reply to a user with /auth, or use /auth <user_id>.")
        return
    if user_id in settings.owner_ids:
        await message.reply("Owner already has full access.")
        return
    await grant(int(user_id), int(message.from_user.id))
    await message.reply(
        f"✅ Authorized user: <code>{int(user_id)}</code>\n"
        "All commands and helper-style forwarding are enabled."
    )


@router.message(Command("unauth"))
async def unauth_user(message: Message):
    if not owner(message):
        return
    target = getattr(message, "reply_to_message", None)
    user_id = getattr(getattr(target, "from_user", None), "id", None) if target else None
    if user_id is None:
        parts = (message.text or "").strip().split()
        if len(parts) >= 2 and parts[1].lstrip("-").isdigit():
            user_id = int(parts[1])
    if not user_id:
        await message.reply("Usage: reply to a user with /unauth, or use /unauth <user_id>.")
        return
    if user_id in settings.owner_ids:
        await message.reply("Owner access cannot be removed.")
        return
    removed = await revoke(int(user_id))
    await message.reply(
        f"{'✅ Revoked' if removed else 'ℹ️ User was not authorized'}: <code>{int(user_id)}</code>"
    )


@router.message(Command("authlist"))
async def auth_list(message: Message):
    if not owner(message):
        return
    rows = await list_authorized()
    if not rows:
        await message.reply("Authorized users: <code>0</code>")
        return
    lines = ["👥 <b>AUTHORIZED USERS</b>", ""]
    for row in rows:
        lines.append(f"• <code>{row['user_id']}</code>")
    await message.reply("\n".join(lines))


@router.message(Command("start"))
async def start(message: Message):
    # Public entry point. The optional Pyrogram userbot never blocks /start.
    helper_state = "ONLINE" if helper_userbot.client else "DISABLED (optional)"
    await message.reply(
        "🇲🇲 <b>မင်္ဂလာပါ။ Bika Adding & Lookup V4 မှ ကြိုဆိုပါတယ်။</b>\n\n"
        "အသုံးပြုနည်း:\n"
        "• Group ထဲမှာ photo/video ပို့ရင် auto lookup လုပ်ပေးပါမယ်။\n"
        "• Media ကို reply ပြန်ပြီး <code>/waifu</code> <code>/w</code> <code>.wa</code> <code>.w</code> "
        "သုံးပြီး manual lookup လုပ်နိုင်ပါတယ်။\n\n"
        f"🤖 Bot API: <code>ONLINE</code>\n"
        f"🔧 Helper Userbot: <code>{helper_state}</code>\n"
        "⚡ Lookup Engine: <code>SQLITE + MONGO</code>\n"
        "🛡 Force Join: <code>/verify</code> ဖြင့် စစ်ဆေးနိုင်ပါတယ်။"
    )

@router.message(Command("ping"))
async def ping(message: Message):
    await message.reply("🏓 <b>PONG</b> — Bot API is responding.")


@router.message(Command("status"))
async def status(message: Message):
    if not await has_admin_access(message):
        return
    helper = await helper_manager.status_text()
    count = await characters.count_documents({})
    helper_state = "ONLINE" if helper_userbot.client else "DISABLED (optional)"
    index_stats = await lookup_index.stats()
    force_status = force_join.status()
    await message.reply(
        "♻ <b>ADDING + LOOKUP V4 STATUS</b>\n"
        f"‣ Total Media : <code>{count:,}</code>\n"
        f"‣ Uptime : <code>{_uptime_text()}</code>\n"
        f"‣ Process Max RAM : <code>{_process_rss_mb():.1f} MB</code>\n"
        f"‣ Adding Group : <code>{settings.adding_chat_id or 'DISABLED'}</code>\n"
        f"‣ Helper Userbot : <code>{helper_state}</code>\n\n"
        "⚡ <b>LOOKUP ENGINE V4</b>\n"
        f"‣ Engine : <code>SQLite + Mongo</code>\n"
        f"‣ SQLite Ready : <code>{'YES' if index_stats.get('ready') else 'NO'}</code>\n"
        f"‣ SQLite Rows : <code>{int(index_stats.get('rows', 0)):,}</code>\n"
        f"‣ RAM Hot Cache : <code>{int(index_stats.get('ram_items', 0)):,} / {settings.lookup_ram_cache_max_items:,}</code>\n"
        f"‣ SQLite Path : <code>{h(settings.lookup_sqlite_path)}</code>\n"
        f"‣ Force Join : <code>{'ACTIVE' if force_status.get('active') else 'OFF'}</code>\n"
        f"‣ Required Channels : <code>{int(force_status.get('targets', 0))}</code>\n\n"
        f"{helper}"
    )

@router.message(Command("stats"))
async def stats(message: Message):
    if not await has_admin_access(message):
        return
    count = await characters.count_documents({})
    index_stats = await lookup_index.stats()
    db_ping = await _ping_db_ms()
    bot_ping = await _ping_bot_ms(message)
    force_status = force_join.status()
    await message.reply(
        "📊 <b>UNIFIED ADDING + LOOKUP V4 STATS</b>\n\n"
        f"‣ Uptime : <code>{_uptime_text()}</code>\n"
        f"‣ DB Ping : <code>{_ms_text(db_ping)}</code>\n"
        f"‣ Bot Ping : <code>{_ms_text(bot_ping)}</code>\n"
        f"‣ Process RAM : <code>{_process_rss_mb():.1f} MB</code>\n"
        f"‣ Total Media : <code>{count:,}</code>\n"
        f"‣ DB : <code>{h(settings.db_name)}</code>\n\n"
        "⚡ <b>LOOKUP ENGINE V4</b>\n"
        f"‣ SQLite Ready : <code>{'YES' if index_stats.get('ready') else 'NO'}</code>\n"
        f"‣ SQLite Rows : <code>{int(index_stats.get('rows', 0)):,}</code>\n"
        f"‣ RAM Hot Cache : <code>{int(index_stats.get('ram_items', 0)):,} / {settings.lookup_ram_cache_max_items:,}</code>\n"
        f"‣ Last Sync : <code>{h(str(index_stats.get('last_updated_ts') or '0'))}</code>\n"
        f"‣ Force Join : <code>{'ACTIVE' if force_status.get('active') else 'OFF'}</code>\n"
        f"‣ Adding Mode : <code>{'forward-only' if settings.adding_chat_id else 'lookup-only'}</code>"
    )

@router.message(Command("helperstatus"))

@router.message(Command("helperstatus"))
async def helper_status(message: Message):
    if not await has_admin_access(message):
        return
    await message.reply(await helper_manager.status_text())


@router.message(Command("addingstatus"))
async def adding_status(message: Message):
    if not await has_admin_access(message):
        return
    await message.reply(
        "📥 <b>Adding Helper</b>\n"
        "Mode: <code>channel-forward only</code>\n"
        f"Adding Group: <code>{settings.adding_chat_id}</code>\n"
        "DM worker/crawler: <code>disabled</code>"
    )


@router.message(F.chat.id == settings.adding_chat_id, F.func(is_ingest_candidate))
async def adding_ingest(message: Message):
    # Adding is intentionally restricted to forwarded channel/source posts.
    # Ordinary media sent directly into the Adding group is ignored.
    is_forwarded = bool(getattr(message, "forward_origin", None) or getattr(message, "forward_from_chat", None))
    helper_user_id = helper_userbot.user_id
    is_helper_inline = bool(helper_user_id and getattr(message.from_user, "id", None) == helper_user_id)
    current_user_id = getattr(getattr(message, "from_user", None), "id", None)
    is_authorized_sender = bool(
        current_user_id and await is_authorized(current_user_id)
    )
    # Allow only the explicitly requested source bots to send original media
    # directly into Adding. Existing forwarded/helper/authorized paths remain
    # unchanged.
    direct_adding_source_bot = current_user_id in {
        8688011915,  # @Characters_Hallow_bot
        8649913814,  # @WaifuxGrabBot
    } and bool(getattr(getattr(message, "from_user", None), "is_bot", False))
    if not is_forwarded and not is_helper_inline and not is_authorized_sender and not direct_adding_source_bot:
        log.info(
            "ADDING skip untrusted media message=%s from_user=%s via_bot=%s",
            message.message_id,
            getattr(getattr(message, "from_user", None), "id", None),
            getattr(getattr(message, "via_bot", None), "username", None),
        )
        return
    trusted_helpers = {helper_userbot.user_id} if helper_userbot.user_id else set()
    if is_authorized_sender and current_user_id:
        trusted_helpers.add(int(current_user_id))
    log.info(
        "ADDING ingest message=%s helper=%s forwarded=%s via_bot=%s caption=%r",
        message.message_id,
        is_helper_inline,
        is_forwarded,
        getattr(getattr(message, "via_bot", None), "username", None),
        (getattr(message, "caption", None) or "")[:180],
    )
    result = await ingest_message(
        message.bot,
        message,
        trusted_user_ids=trusted_helpers,
    )
    if result:
        status = result.get("status") if isinstance(result, dict) else "unknown"
        log.info(
            "INGESTED adding message=%s chat=%s source=resolved status=%s",
            message.message_id,
            message.chat.id,
            status,
        )
        if isinstance(result, dict):
            saved_doc = result.get("document") or {}
            if saved_doc:
                try:
                    await lookup_index.upsert_document(saved_doc)
                except Exception:
                    log.exception(
                        "LOOKUP SQLITE snapshot upsert failed message=%s",
                        message.message_id,
                    )
            notice = format_ingest_notice(result)
            if notice:
                try:
                    await message.reply(
                        notice,
                        disable_web_page_preview=True,
                    )
                except Exception:
                    log.exception(
                        "INGEST notification failed message=%s status=%s",
                        message.message_id,
                        status,
                    )
    else:
        log.warning("ADDING ingest did not save message=%s chat=%s", message.message_id, message.chat.id)


@router.message(
    F.func(lambda m: bool(getattr(m.chat, "id", 0) != settings.adding_chat_id)),
    F.func(is_media),
)
async def lookup_media(message: Message):
    if not settings.auto_lookup_enabled:
        return
    if message.chat.type == "private" and not settings.lookup_in_private:
        return
    if message.chat.type != "private" and not settings.lookup_in_groups:
        return

    if not await enforce_lookup_access(message):
        return

    # Senpai direct Bot-to-Bot messages: Telegram delivers the original
    # message from @SenpaiCatcherBot as a bot sender (ID 8532697507).
    # Handle this path explicitly so it never depends on forward metadata.
    # Forwarded messages and every other source keep their existing routing.
    direct_senpai_bot = (
        getattr(getattr(message, "from_user", None), "id", None) == 8532697507
        and bool(getattr(getattr(message, "from_user", None), "is_bot", False))
    )
    # Auto lookup uses source-first matching, then the exact Telegram UID
    # global fallback. This recovers media forwarded from the Adding Group or
    # another intermediary while preserving source separation because only a
    # unique exact UID is accepted globally. Similarity fallback stays guarded.
    auto_global_exact = bool(settings.v3_global_exact_fallback)
    senpai_auto_global_uid = (
        direct_senpai_bot
        or resolve_source_collection(message) == "items_senpai_catcher"
        or auto_global_exact
    )
    lookup_target = message
    # Senpai may send its media as a reply to another message. For this bot-to-bot
    # path, always treat the actual incoming Senpai media as the lookup target.
    if senpai_auto_global_uid and is_media(message) and getattr(message, "reply_to_message", None):
        lookup_target = message.model_copy(update={"reply_to_message": None})
    doc, reason = await lookup_message(
        message.bot,
        lookup_target,
        allow_global_fallback=senpai_auto_global_uid,
    )
    log.info(
        "LOOKUP chat=%s message=%s result=%s reason=%s",
        message.chat.id,
        message.message_id,
        bool(doc),
        reason,
    )
    if doc:
        await message.reply(
            format_result(doc),
            disable_web_page_preview=True,
            reply_markup=result_buttons(
                type(
                    "LookupItem",
                    (),
                    {
                        "command": doc.get("command", "/name"),
                        "name": doc.get("name", ""),
                    },
                )()
            ),
        )
    elif settings.reply_not_found:
        await message.reply("❌ Character not found.")


async def _manual_lookup(message: Message):
    if not await enforce_lookup_access(message):
        return

    target = getattr(message, "reply_to_message", None)
    if not target or not is_media(target):
        await message.reply("❌ Reply to a character media with .w / .wa / .waifu.")
        return
    doc, reason = await lookup_message(message.bot, target, allow_global_fallback=True)
    log.info(
        "MANUAL LOOKUP chat=%s message=%s result=%s reason=%s",
        message.chat.id,
        message.message_id,
        bool(doc),
        reason,
    )
    if doc:
        await message.reply(
            format_result(doc),
            disable_web_page_preview=True,
            reply_markup=result_buttons(
                type(
                    "LookupItem",
                    (),
                    {
                        "command": doc.get("command", "/name"),
                        "name": doc.get("name", ""),
                    },
                )()
            ),
        )
    else:
        await message.reply("❌ Character not found.")


@router.message(F.text.regexp(r"^(?:\.w|/w|\.wa|/wa|\.waifu|/waifu)(?:\s|$)"))
async def manual_lookup(message: Message):
    await _manual_lookup(message)


HELPER_COMMANDS = [
    "helper", "addhelper", "helperstatus", "addhelperstatus", "stophelper",
    "resethelperprogress",

    # Inline/source-bot Adding commands (must stay in sync with HelperManager.SOURCES).
    "startcatchbot", "resumecatchbot",
    "startcatcherbot", "resumecatcherbot",
    "startcharactercatcher", "resumecharactercatcher",
    "starthallowbot", "resumehallowbot",
    "starthallow", "resumehallow",
    "startcapturebot", "resumecapturebot",
    "startcapture", "resumecapture",
    "startseizerbot", "resumeseizerbot",
    "startseizer", "resumeseizer",
    "startgrabbot", "resumegrabbot",
    "startgrabyourwaifu", "resumegrabyourwaifu",
    "starthusbandograbberbot", "resumehusbandograbberbot",
    "starthusbandograbber", "resumehusbandograbber",
    "starttakersbot", "resumetakersbot",
    "starttakers", "resumetakers",
    "startsmashbot", "resumesmashbot",
    "startsmash", "resumesmash",
    "startwaifuxgrabbot", "resumewaifuxgrabbot",
    "startwaifuxgrab", "resumewaifuxgrab",
    "startwaifux", "resumewaifux",
    "startcatchyourwaifubot", "resumecatchyourwaifubot",
    "startcatchyourwaifu", "resumecatchyourwaifu",
    "startcatchyourhusbandobot", "resumecatchyourhusbandobot",
    "startcatchyourhusbando", "resumecatchyourhusbando",
    "startwaifugrabberbot", "resumewaifugrabberbot",
    "startwaifugrabber", "resumewaifugrabber",
    "startzorobot", "resumezorobot",
    "startzoro", "resumezoro",
    "startpickerbot", "resumepickerbot",
    "startpicker", "resumepicker",
    "startsenpaibot", "resumesenpaibot",
    "startbika", "resumebika",
    "startbikabot", "resumebikabot",
    "startzicekobot", "resumezicekobot",
    "startziceko", "resumeziceko",
    "startorinbot", "resumeorinbot",
    "startorin", "resumeorin",
    "startorinx", "resumeorinx",
    "startdaobot", "resumedaobot",
    "startdao", "resumedao",
    "startdonghua", "resumedonghua",

    # Forward-source Adding commands (must stay in sync with HelperManager.FORWARD_SOURCES).
    "startfwhallowbot", "resumefwhallowbot",
    "startfwhallow", "resumefwhallow",
    "startfwcapturebot", "resumefwcapturebot",
    "startfwcapture", "resumefwcapture",
    "startfwseizerbot", "resumefwseizerbot",
    "startfwseizer", "resumefwseizer",
    "startfwwaifuxbot", "resumefwwaifuxbot",
    "startfwwaifux", "resumefwwaifux",
    "startfwsenaibot", "resumefwsenaibot",
    "startfwbikabot", "resumefwbikabot",
    "startfwbika", "resumefwbika",
    "startfwzicekobot", "resumefwzicekobot",
    "startfwziceko", "resumefwziceko",
    "startfworinbot", "resumefworinbot",
    "startfworin", "resumefworin",
    "startfworinx", "resumefworinx",
    "startfwdaobot", "resumefwdaobot",
    "startfwdao", "resumefwdao",
    "startfwdonghua", "resumefwdonghua",

    # Catch FW extras.
    "startfwcatchbot", "startfwcatchbotvd", "resumefwcatchbot",
    "startfwcatch", "resumefwcatch",
]


@router.message(Command(*HELPER_COMMANDS))
async def helper_commands(message: Message):
    if not await has_admin_access(message):
        return
    await helper_manager.handle_command(message)


async def lookup_index_sync_worker(stop_event: asyncio.Event):
    """Build the local snapshot in the background so Render can bind its port first."""
    try:
        await lookup_index.ensure_ready()
        log.info(
            "LOOKUP V4 index ready path=%s ram_items=%s",
            settings.lookup_sqlite_path,
            lookup_index.ram.size(),
        )
    except asyncio.CancelledError:
        raise
    except Exception:
        # Exact Mongo lookup remains available while the local snapshot is unavailable.
        log.exception("LOOKUP SQLITE initial snapshot build failed")

    interval = max(30, int(settings.lookup_index_sync_seconds or 300))
    while not stop_event.is_set():
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=interval)
            continue
        except asyncio.TimeoutError:
            pass

        try:
            await lookup_index.sync_from_mongo()
            log.info(
                "LOOKUP SQLITE snapshot sync complete rows=%s ram=%s",
                (await lookup_index.stats()).get("rows", 0),
                lookup_index.ram.size(),
            )
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("LOOKUP SQLITE snapshot sync failed")


async def cleanup(bot: Bot):
    await lookup_index.close()
    await close()
    await bot.session.close()


async def run():
    if not settings.bot_token:
        raise RuntimeError("BOT_TOKEN is required")
    if not settings.mongo_uri:
        raise RuntimeError("MONGO_URI is required")
    if not settings.owner_ids:
        raise RuntimeError("OWNER_IDS is required")
    # ADDING_CHAT_ID is optional for LookupV4 lookup-only deployments.
    # When it is missing, the Adding-group ingest/Helper forwarding paths stay
    # disabled, while Bot API lookup, MongoDB, SQLite snapshot and Force Join
    # continue to run normally. Supplying ADDING_CHAT_ID later re-enables them
    # without any code change.
    if not settings.adding_chat_id:
        log.warning(
            "ADDING_CHAT_ID is not configured; running in lookup-only mode "
            "(Adding-group ingest/Helper forwarding disabled)"
        )

    mode = settings.run_mode
    if mode not in {"auto", "polling", "webhook"}:
        raise RuntimeError("RUN_MODE must be auto, polling, or webhook")
    webhook = mode == "webhook" or (mode == "auto" and bool(settings.public_url))
    if webhook and not settings.public_url:
        raise RuntimeError("PUBLIC_URL is required in webhook mode")

    bot = Bot(
        settings.bot_token,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )
    dp = Dispatcher()
    dp.include_router(router)

    index_sync_stop = asyncio.Event()
    index_sync_task = asyncio.create_task(
        lookup_index_sync_worker(index_sync_stop)
    )

    if webhook:
        path = settings.webhook_path if settings.webhook_path.startswith("/") else "/" + settings.webhook_path
        app = web.Application()
        app.router.add_get(
            "/healthz",
            lambda _: web.json_response({
                "ok": True,
                "service": "unified-adding-lookup",
                "mode": "webhook",
                "adding": "forward-only",
            }),
        )
        SimpleRequestHandler(
            dispatcher=dp,
            bot=bot,
            secret_token=settings.webhook_secret,
        ).register(app, path=path)
        setup_application(app, dp, bot=bot)

        runner = web.AppRunner(app)
        await runner.setup()
        site = web.TCPSite(runner, settings.host, settings.port)
        await site.start()
        log.info("HTTP port bound on %s:%s", settings.host, settings.port)

        # Set the Telegram webhook immediately after the port is available.
        # Local snapshot/Mongo index building happens independently in the background.
        try:
            await bot.set_webhook(
                settings.public_url + path,
                secret_token=settings.webhook_secret,
                drop_pending_updates=True,
            )
            log.info("Webhook ready: %s%s", settings.public_url, path)
        except Exception:
            log.exception("Webhook setup failed")

        try:
            await ensure_indexes()
            await ensure_auth_indexes()
            log.info("Mongo indexes ready")
        except Exception:
            log.exception("Mongo/index initialization failed; exact Mongo lookup remains available")

        try:
            await helper_userbot.start()
            helper_manager.bind()
            log.info("Helper userbot ready")
        except Exception:
            log.exception("Helper userbot startup failed; lookup bot will continue")
        try:
            await asyncio.Event().wait()
        finally:
            index_sync_stop.set()
            index_sync_task.cancel()
            await asyncio.gather(index_sync_task, return_exceptions=True)
            await helper_userbot.stop()
            await cleanup(bot)
            await runner.cleanup()
    else:
        await bot.delete_webhook(drop_pending_updates=False)
        app = web.Application()
        app.router.add_get(
            "/healthz",
            lambda _: web.json_response({
                "ok": True,
                "service": "unified-adding-lookup",
                "mode": "polling",
                "adding": "forward-only",
            }),
        )
        runner = web.AppRunner(app)
        await runner.setup()
        await web.TCPSite(runner, settings.host, settings.port).start()
        log.info("HTTP port bound on %s:%s", settings.host, settings.port)

        try:
            await ensure_indexes()
            await ensure_auth_indexes()
            log.info("Mongo indexes ready")
        except Exception:
            log.exception("Mongo/index initialization failed; polling will continue")

        try:
            await helper_userbot.start()
            helper_manager.bind()
            log.info("Helper userbot ready")
        except Exception:
            log.exception("Helper userbot startup failed; polling will continue")

        log.info("Polling ready; Adding mode=forward-only")
        try:
            await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
        finally:
            index_sync_stop.set()
            index_sync_task.cancel()
            await asyncio.gather(index_sync_task, return_exceptions=True)
            await helper_userbot.stop()
            await cleanup(bot)
            await runner.cleanup()


if __name__ == "__main__":
    asyncio.run(run())
