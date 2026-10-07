from __future__ import annotations

import asyncio
import logging
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "namebotv3"))
sys.path.insert(0, str(ROOT))

from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.client.telegram import TelegramAPIServer
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command
from aiogram.types import Message
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application

from unified.config import settings
from unified.store import db, characters, close, ensure_indexes
from unified.uid_index import ensure_uid_index, get_meta, set_meta, upsert_documents
from unified.hash_index import warm_photo_hash_index, remember_document
from unified.auth import ensure_auth_indexes, is_authorized, grant, revoke, list_authorized, get_global_lookup_enabled, set_global_lookup_enabled
from unified.ingest import ingest_message
from unified.lookup import lookup_message
from helper.runtime import HelperUserbot
from helper.manager import HelperManager
from services.result_formatter import result_buttons
from unified.services.force_join import require_join, send_dm_verification, set_force_join_enabled, force_join_status, router as force_join_router
from services.source_resolver import resolve_source_collection
from utils.text import h, first_token
from unified.status import build_ping_text, build_stats_text, build_status_text, metrics
from unified.miniapp import register_miniapp

logging.basicConfig(
    level=getattr(logging, settings.log_level, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
log = logging.getLogger("unified")

router = Router(name="unified")
helper_userbot = HelperUserbot()
helper_manager = HelperManager(helper_userbot)


async def _backfill_uid_index() -> None:
    """Incrementally warm SQLite from Mongo and resume safely after restart.

    MongoDB remains authoritative. The checkpoint only controls which Mongo
    documents the accelerator has already scanned; normal ingest hot-sync keeps
    newly inserted/updated records current while the backfill is running.
    """
    from bson import ObjectId

    batch_size = settings.uid_index_backfill_batch
    meta_complete = "backfill_complete"
    meta_last_id = "backfill_last_id"

    try:
        if await get_meta(meta_complete) == "1":
            log.info("UID INDEX backfill already complete; hot-sync remains active")
            return

        last_id = await get_meta(meta_last_id)
        query: dict = {
            "$or": [
                {"file_unique_ids.0": {"$exists": True}},
                {"telegram_file_unique_id": {"$exists": True, "$ne": ""}},
            ]
        }
        if last_id:
            try:
                query["_id"] = {"$gt": ObjectId(last_id)}
            except Exception:
                log.warning("UID INDEX invalid resume checkpoint=%r; restarting scan", last_id)

        cursor = characters.find(
            query,
            {
                "_id": 1,
                "name": 1,
                "command": 1,
                "source_key": 1,
                "media_type": 1,
                "file_unique_ids": 1,
                "telegram_file_unique_id": 1,
                "updated_at": 1,
            },
            batch_size=batch_size,
        ).sort("_id", 1)

        batch: list[dict] = []
        processed = 0
        async for doc in cursor:
            batch.append(doc)
            if len(batch) >= batch_size:
                count = await upsert_documents(batch)
                last_doc_id = batch[-1].get("_id")
                if isinstance(last_doc_id, ObjectId):
                    await set_meta(meta_last_id, str(last_doc_id))
                processed += len(batch)
                log.info("UID INDEX backfill batch docs=%s rows=%s processed=%s", len(batch), count, processed)
                batch.clear()

        if batch:
            count = await upsert_documents(batch)
            last_doc_id = batch[-1].get("_id")
            if isinstance(last_doc_id, ObjectId):
                await set_meta(meta_last_id, str(last_doc_id))
            processed += len(batch)
            log.info("UID INDEX backfill final docs=%s rows=%s processed=%s", len(batch), count, processed)

        await set_meta(meta_complete, "1")
        log.info("UID INDEX backfill complete processed=%s", processed)
    except asyncio.CancelledError:
        raise
    except Exception:
        log.exception("UID INDEX backfill failed; Mongo remains authoritative and checkpoint will resume")


async def _start_uid_index_backfill() -> None:
    # Backfill is deliberately fire-and-forget: the bot becomes ready immediately
    # and every SQLite miss still falls through to Mongo for correctness.
    asyncio.create_task(_backfill_uid_index())


async def _start_hash_index_warm() -> None:
    # Mongo remains authoritative. The RAM hash index is only a candidate
    # accelerator and warms in the background without blocking bot startup.
    asyncio.create_task(warm_photo_hash_index(characters))


def owner(message: Message) -> bool:
    return bool(message.from_user and message.from_user.id in settings.owner_ids)


async def has_admin_access(message: Message) -> bool:
    user = getattr(message, "from_user", None)
    if not user:
        return False
    return owner(message) or await is_authorized(user.id)


async def global_lookup_allowed(message: Message) -> bool:
    # Private-chat auto/manual lookup is independent of public-group Global mode.
    # Global OFF only restricts public groups; Force Join is still checked by
    # the lookup handlers themselves.
    if message.chat.type == "private":
        return True
    if await get_global_lookup_enabled():
        return True
    if owner(message):
        return True
    doc = await db.settings.find_one({"key": f"gapprove:{int(message.chat.id)}"})
    return bool(doc and doc.get("enabled", True))


GLOBAL_OFF_TEXT = (
    "⚠️ Global lookup is currently disabled here.\\n\\n"
    "Please use @BikaWaifuCheatBot Main Bot for lookup."
)


def is_media(message: Message) -> bool:
    return bool(
        getattr(message, "photo", None)
        or getattr(message, "video", None)
        or getattr(message, "animation", None)
        or getattr(message, "document", None)
    )


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

async def _safe_reply(message: Message, text: str, **kwargs):
    """Reply safely when Telegram has revoked text-send permissions."""
    try:
        return await message.reply(text, **kwargs)
    except (TelegramBadRequest, TelegramForbiddenError) as exc:
        error_text = str(exc).lower()
        if (
            "not enough rights to send text messages" in error_text
            or "bot was kicked" in error_text
            or "forbidden" in error_text
        ):
            log.warning(
                "TELEGRAM REPLY SKIPPED chat=%s message=%s error=%s",
                getattr(getattr(message, "chat", None), "id", None),
                getattr(message, "message_id", None),
                str(exc),
            )
            return None
        raise


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
    # Group Force Join sends users here through a Telegram deep-link.
    # Keep the normal /start welcome screen unchanged for every other start.
    parts = (message.text or "").strip().split(maxsplit=1)
    payload = parts[1].strip().lower() if len(parts) > 1 else ""
    if payload in {"forcejoin", "fj", "verify"}:
        await send_dm_verification(message)
        return

    await message.reply(
        "👋 <b>Welcome to Bika Adding & Helper</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        "⚡ <b>Fast Character Lookup</b>\n"
        "• Send a photo/video for auto lookup.\n"
        "• Reply to media with <code>.w</code>, <code>.wa</code> or <code>.waifu</code>.\n\n"
        "🛠 <b>System</b>\n"
        "• <code>/status</code> — runtime & database status\n"
        "• <code>/stats</code> — performance statistics\n"
        "• <code>/ping</code> — Bot/Mongo latency\n\n"
        "Powered by <b>Bika</b>."
    )


@router.message(Command("global"))
async def global_lookup_command(message: Message):
    if not owner(message):
        return
    parts = (message.text or "").strip().split()
    value = parts[1].lower() if len(parts) > 1 else "status"
    if value in {"on", "enable", "enabled", "1", "true"}:
        await set_global_lookup_enabled(True, message.from_user.id)
        await message.reply("✅ Global lookup is now <b>ON</b>.")
    elif value in {"off", "disable", "disabled", "0", "false"}:
        await set_global_lookup_enabled(False, message.from_user.id)
        await message.reply("🔒 Global lookup is now <b>OFF</b>.\\nOnly the owner and owner-approved groups can use lookup.")
    elif value in {"status", "state"}:
        enabled = await get_global_lookup_enabled()
        await message.reply(f"🌐 Global lookup: <b>{'ON' if enabled else 'OFF'}</b>")
    else:
        await message.reply("Usage: <code>/global on</code>, <code>/global off</code>, or <code>/global status</code>.")


@router.message(Command("gapprove"))
async def gapprove(message: Message):
    if not owner(message):
        return
    if message.chat.type == "private":
        await message.reply("Use /gapprove inside the target group.")
        return
    await db.settings.update_one(
        {"key": f"gapprove:{int(message.chat.id)}"},
        {"$set": {"enabled": True, "chat_id": int(message.chat.id)}, "$setOnInsert": {"created_at": __import__("datetime").datetime.now(__import__("datetime").timezone.utc)}},
        upsert=True,
    )
    await message.reply("✅ This group is approved for lookup.")


@router.message(Command("gunapprove"))
async def gunapprove(message: Message):
    if not owner(message):
        return
    if message.chat.type == "private":
        await message.reply("Use /gunapprove inside the target group.")
        return
    await db.settings.update_one(
        {"key": f"gapprove:{int(message.chat.id)}"},
        {"$set": {"enabled": False, "chat_id": int(message.chat.id)}, "$setOnInsert": {"created_at": __import__("datetime").datetime.now(__import__("datetime").timezone.utc)}},
        upsert=True,
    )
    await message.reply("✅ This group is no longer approved for lookup.")


@router.message(Command("fjoin"))
async def fjoin(message: Message):
    """Owner-only runtime Force Join control; DM only."""
    if not owner(message):
        return
    if message.chat.type != "private":
        await message.reply("❌ /fjoin can only be used in the bot DM.")
        return

    args = str(getattr(message, "text", "") or "").split(maxsplit=1)
    action = args[1].strip().lower() if len(args) > 1 else "status"

    if action not in {"on", "off", "status"}:
        await message.reply(
            "Usage: <code>/fjoin on</code>\n"
            "<code>/fjoin off</code>\n"
            "<code>/fjoin status</code>"
        )
        return

    channels = bool(settings.force_join_chat_ids or settings.force_join_chat_id)
    if not channels:
        await message.reply(
            "⚠️ Force Join channels are not configured. "
            "Set FORCE_JOIN_CHAT_IDS/URLS (or legacy FORCE_JOIN_CHAT_ID/URL) first."
        )
        return

    if action == "status":
        enabled = await force_join_status()
        await message.reply(
            "🔐 <b>Force Join</b>\n\n"
            f"Status: <b>{'ON' if enabled else 'OFF'}</b>\n"
            f"Channels: <code>{len(settings.force_join_chat_ids) or (1 if settings.force_join_chat_id else 0)}</code>\n"
            "Positive join cache: <b>ON</b>\n"
            f"Positive TTL: <code>{settings.force_join_positive_cache_seconds}s</code>"
        )
        return

    enabled = await set_force_join_enabled(action == "on")
    await message.reply(
        f"✅ <b>Force Join {'enabled' if enabled else 'disabled'}.</b>\n\n"
        f"Positive join cache: <b>ON</b> ({settings.force_join_positive_cache_seconds}s)\n"
        "Verification cache cleared."
    )


@router.message(Command("status"))
async def status(message: Message):
    if not owner(message):
        return
    await message.reply(await build_status_text(message))


@router.message(Command("stats"))
async def stats(message: Message):
    if not owner(message):
        return
    helper_state = "ONLINE" if helper_userbot.client else "OFFLINE"
    await message.reply(
        await build_stats_text(
            message,
            helper_state=helper_state,
        )
    )


@router.message(Command("ping"))
async def ping(message: Message):
    await message.reply(await build_ping_text(message))


@router.message(Command("helperstatus"))
async def helper_status(message: Message):
    if not owner(message):
        return
    await message.reply(await helper_manager.status_text())


@router.message(Command("addingstatus"))
async def adding_status(message: Message):
    if not owner(message):
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
    if isinstance(result, dict) and result.get("document"):
        try:
            remember_document(result["document"])
        except Exception:
            log.exception(
                "HASH RAM hot-sync failed message=%s",
                message.message_id,
            )
    if result:
        status = result.get("status") if isinstance(result, dict) else "unknown"
        metrics.record_ingest(status)
        log.info(
            "INGESTED adding message=%s chat=%s source=resolved status=%s",
            message.message_id,
            message.chat.id,
            status,
        )
        if isinstance(result, dict):
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
    if not await global_lookup_allowed(message):
        await message.reply(GLOBAL_OFF_TEXT)
        return
    if not await require_join(message):
        return
    if not settings.auto_lookup_enabled:
        return
    if message.chat.type == "private" and not settings.lookup_in_private:
        return
    if message.chat.type != "private" and not settings.lookup_in_groups:
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
    lookup_started = time.perf_counter()
    try:
        doc, reason = await lookup_message(
            message.bot,
            lookup_target,
            allow_global_fallback=senpai_auto_global_uid,
        )
    except Exception:
        metrics.record_lookup(
            (time.perf_counter() - lookup_started) * 1000,
            hit=False,
            error=True,
        )
        raise
    else:
        metrics.record_lookup(
            (time.perf_counter() - lookup_started) * 1000,
            hit=bool(doc),
        )
    log.info(
        "LOOKUP chat=%s message=%s result=%s reason=%s",
        message.chat.id,
        message.message_id,
        bool(doc),
        reason,
    )
    if doc:
        await _safe_reply(
            message,
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
        await _safe_reply(message, "❌ Character not found.")


async def _manual_lookup(message: Message):
    if not await global_lookup_allowed(message):
        await message.reply(GLOBAL_OFF_TEXT)
        return
    if not await require_join(message):
        return
    target = getattr(message, "reply_to_message", None)
    if not target or not is_media(target):
        await message.reply("❌ Reply to a character media with .w / .wa / .waifu.")
        return
    lookup_started = time.perf_counter()
    try:
        doc, reason = await lookup_message(message.bot, target, allow_global_fallback=True)
    except Exception:
        metrics.record_lookup(
            (time.perf_counter() - lookup_started) * 1000,
            hit=False,
            error=True,
        )
        raise
    else:
        metrics.record_lookup(
            (time.perf_counter() - lookup_started) * 1000,
            hit=bool(doc),
        )
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
    "startfwpickerbot", "resumefwpickerbot",
    "startfwpicker", "resumefwpicker",
    "startfwkairobot", "resumefwkairobot",
    "startfwkairo", "resumefwkairo",
    "startfwcatchbot", "startfwcatchbotvd", "resumefwcatchbot",
    "startfwcatch", "resumefwcatch",
]


@router.message(Command(*HELPER_COMMANDS))
async def helper_commands(message: Message):
    if not await has_admin_access(message):
        return
    await helper_manager.handle_command(message)


async def cleanup(bot: Bot):
    await close()
    await bot.session.close()


async def run():
    if not settings.bot_token:
        raise RuntimeError("BOT_TOKEN is required")
    if not settings.mongo_uri:
        raise RuntimeError("MONGO_URI is required")
    if not settings.owner_ids:
        raise RuntimeError("OWNER_IDS is required")
    if not settings.adding_chat_id:
        raise RuntimeError("ADDING_CHAT_ID is required")

    mode = settings.run_mode
    if mode not in {"auto", "polling", "webhook"}:
        raise RuntimeError("RUN_MODE must be auto, polling, or webhook")
    webhook = mode == "webhook" or (mode == "auto" and bool(settings.public_url))
    if webhook and not settings.public_url:
        raise RuntimeError("PUBLIC_URL is required in webhook mode")

    await ensure_indexes()
    await ensure_uid_index()
    await _start_uid_index_backfill()
    await _start_hash_index_warm()
    await ensure_auth_indexes()
    await helper_userbot.start()
    helper_manager.bind()

    bot_session = None
    if settings.bot_api_base_url:
        bot_api = TelegramAPIServer.from_base(
            settings.bot_api_base_url,
            is_local=settings.bot_api_is_local,
        )
        bot_session = AiohttpSession(
            api=bot_api,
            limit=settings.bot_api_session_limit,
        )
        log.info(
            "Telegram Bot API server configured base=%s local=%s session_limit=%s",
            settings.bot_api_base_url,
            settings.bot_api_is_local,
            settings.bot_api_session_limit,
        )

    bot = Bot(
        settings.bot_token,
        session=bot_session,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )
    dp = Dispatcher()
    dp.include_router(force_join_router)
    dp.include_router(router)

    if webhook:
        path = settings.webhook_path if settings.webhook_path.startswith("/") else "/" + settings.webhook_path
        app = web.Application()
        register_miniapp(app)
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
        await bot.set_webhook(
            settings.public_url + path,
            secret_token=settings.webhook_secret,
            drop_pending_updates=True,
        )
        log.info("Webhook ready: %s%s", settings.public_url, path)
        try:
            await asyncio.Event().wait()
        finally:
            await helper_userbot.stop()
            await cleanup(bot)
            await runner.cleanup()
    else:
        await bot.delete_webhook(drop_pending_updates=True)
        app = web.Application()
        register_miniapp(app)
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
        log.info("Polling ready; Adding mode=forward-only")
        try:
            await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
        finally:
            await helper_userbot.stop()
            await cleanup(bot)
            await runner.cleanup()


if __name__ == "__main__":
    asyncio.run(run())
