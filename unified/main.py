from __future__ import annotations

import asyncio
import html
import logging
from pathlib import Path

from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.client.telegram import TelegramAPIServer
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError
from aiogram.filters import Command
from aiogram.types import Message
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application

from helper.manager import FORWARD_SOURCES, SOURCES, HelperManager
from helper.runtime import HelperUserbot
from unified.auth import ensure_auth_indexes, grant, is_authorized, list_authorized, revoke
from unified.config import settings
from unified.ingest import ingest_message
from helper.registry import ensure_registry_indexes, load_registry
from unified.source_resolver import resolve_source_collection
from unified.source_whitelist import is_allowed_source
from unified.status import build_ping_text, build_stats_text, build_status_text, metrics
from unified.store import close, ensure_indexes

log = logging.getLogger("unified-adding")

router = Router(name="adding")
helper_userbot = HelperUserbot()
helper_manager = HelperManager(helper_userbot)


def owner(message: Message) -> bool:
    return bool(message.from_user and message.from_user.id in settings.owner_ids)


async def has_admin_access(message: Message) -> bool:
    user = getattr(message, "from_user", None)
    if user is None:
        return False
    return owner(message) or await is_authorized(getattr(user, "id", None))


def is_media(message: Message) -> bool:
    return bool(
        getattr(message, "photo", None)
        or getattr(message, "video", None)
        or getattr(message, "animation", None)
        or getattr(message, "document", None)
    )


def is_ingest_candidate(message: Message) -> bool:
    if is_media(message):
        return True
    text = str(getattr(message, "text", None) or getattr(message, "caption", None) or "")
    if not text.strip():
        return False
    user = getattr(message, "from_user", None)
    if helper_userbot.user_id and getattr(user, "id", None) == helper_userbot.user_id:
        return True
    if getattr(user, "is_bot", False) and resolve_source_collection(message):
        return True
    return bool(getattr(message, "forward_origin", None) or getattr(message, "forward_from_chat", None))


def _esc(value: object) -> str:
    return html.escape("" if value is None else str(value), quote=False)


def format_ingest_notice(result: dict) -> str:
    status = str(result.get("status") or "").lower()
    doc = result.get("document") or {}
    name = _esc(doc.get("name") or "Unknown")
    character_id = _esc(doc.get("character_id") or "—")
    source = _esc(doc.get("source_key") or "unknown")
    command = _esc(doc.get("command") or "/name")
    media_type = _esc(doc.get("media_type") or "unknown")

    if status == "already_added":
        return (
            "✅ <b>Already added</b>\n\n"
            f"Card ID: <code>{character_id}</code>\n"
            f"Name: <code>{name}</code>\n"
            f"Source: <code>{source}</code>"
        )
    if status == "unchanged":
        return "✅ <b>Already saved</b>"
    if status == "saved":
        return (
            "✅ <b>CHARACTER SAVED</b>\n\n"
            f"Name: <code>{name}</code>\n"
            f"ID: <code>{character_id}</code>\n"
            f"Command: <code>{command}</code>\n"
            f"Source: <code>{source}</code>\n"
            f"Media: <code>{media_type}</code>"
        )
    if status == "updated":
        changes = list(result.get("changes") or [])
        details = "\n".join(f"• {_esc(item)}" for item in changes[:10]) or "• record fields changed"
        return (
            "🔄 <b>CHARACTER UPDATED</b>\n\n"
            f"Name: <code>{name}</code>\n"
            f"ID: <code>{character_id}</code>\n"
            f"Source: <code>{source}</code>\n"
            f"Media: <code>{media_type}</code>\n\n"
            f"<b>Updated:</b>\n{details}"
        )
    if str(result.get("reason") or "") == "edit_target_not_found":
        return (
            "⚠️ <b>EDIT SKIPPED</b>\n\n"
            f"Card ID: <code>{character_id}</code>\n"
            f"Source: <code>{source}</code>\n"
            "No existing record with this ID was found in this source DB."
        )
    return ""


async def _safe_reply(message: Message, text: str, **kwargs):
    try:
        return await message.reply(text, **kwargs)
    except (TelegramBadRequest, TelegramForbiddenError) as exc:
        lowered = str(exc).lower()
        if "forbidden" in lowered or "not enough rights" in lowered or "bot was kicked" in lowered:
            log.warning(
                "reply skipped chat=%s message=%s error=%s",
                getattr(message.chat, "id", None),
                getattr(message, "message_id", None),
                exc,
            )
            return None
        raise


@router.message(Command("start"))
async def start(message: Message):
    await message.reply(
        "👋 <b>Welcome to Bika Adding & Helper</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        "📥 <b>Adding-only mode</b>\n"
        "Trusted source posts are parsed and saved into MongoDB.\n"
        "No media matching, search engine, or fingerprint worker runs here.\n\n"
        "🛠 <b>Owner Tools</b>\n"
        "• <code>/addingstatus</code>\n"
        "• <code>/stats</code>\n"
        "• <code>/ping</code>\n\n"
        "Powered by <b>Bika</b>."
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
            if raw.lstrip("-").isdigit():
                user_id = int(raw)
            elif raw.startswith("@"):
                try:
                    user_id = getattr(await message.bot.get_chat(raw), "id", None)
                except Exception:
                    user_id = None
    if not user_id:
        await message.reply("Usage: reply to a user with /auth, or /auth <user_id>.")
        return
    if int(user_id) in settings.owner_ids:
        await message.reply("Owner already has full access.")
        return
    await grant(int(user_id), int(message.from_user.id))
    await message.reply(f"✅ Authorized: <code>{int(user_id)}</code>")


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
        await message.reply("Usage: reply to a user with /unauth, or /unauth <user_id>.")
        return
    if int(user_id) in settings.owner_ids:
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
    await message.reply(
        "\n".join(["👥 <b>AUTHORIZED USERS</b>", ""] + [f"• <code>{row['user_id']}</code>" for row in rows])
    )


@router.message(Command("status"))
async def status(message: Message):
    if not owner(message):
        return
    await message.reply(
        await build_status_text(
            message,
            helper_state="ONLINE" if helper_userbot.client else "OFFLINE",
        )
    )


@router.message(Command("stats"))
async def stats(message: Message):
    if not owner(message):
        return
    await message.reply(
        await build_stats_text(
            message,
            helper_state="ONLINE" if helper_userbot.client else "OFFLINE",
        )
    )


@router.message(Command("ping"))
async def ping(message: Message):
    await message.reply(await build_ping_text(message))


@router.message(Command("helperstatus", "addhelperstatus"))
async def helper_status(message: Message):
    if not await has_admin_access(message):
        return
    await message.reply(await helper_manager.status_text())


@router.message(Command("addingstatus"))
async def adding_status(message: Message):
    if not owner(message):
        return
    await message.reply(
        "📥 <b>ADDING HELPER</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "Mode: <code>adding-only</code>\n"
        f"Adding Group: <code>{settings.adding_chat_id}</code>\n"
        f"Helper: <code>{'ONLINE' if helper_userbot.client else 'OFFLINE'}</code>\n"
        "Storage: <code>MongoDB</code>\n"
        "Media work: <code>metadata + Telegram UID only</code>"
    )


@router.message(F.chat.id == settings.adding_chat_id, F.func(is_ingest_candidate))
async def adding_ingest(message: Message):
    user = getattr(message, "from_user", None)
    current_user_id = getattr(user, "id", None)
    helper_id = helper_userbot.user_id
    is_helper = bool(helper_id and current_user_id == helper_id)
    is_authorized_sender = bool(current_user_id and await is_authorized(int(current_user_id)))
    forwarded = bool(getattr(message, "forward_origin", None) or getattr(message, "forward_from_chat", None))
    direct_source_bot = bool(getattr(user, "is_bot", False) and resolve_source_collection(message))
    trusted = is_helper or is_authorized_sender or direct_source_bot

    if forwarded and not trusted and not is_allowed_source(message):
        log.warning("ADDING rejected source message=%s user=%s", message.message_id, current_user_id)
        return
    if not forwarded and not trusted:
        log.info("ADDING rejected untrusted message=%s user=%s", message.message_id, current_user_id)
        return

    trusted_users = {int(helper_id)} if helper_id else set()
    if is_authorized_sender and current_user_id:
        trusted_users.add(int(current_user_id))

    result = await ingest_message(message.bot, message, trusted_user_ids=trusted_users)
    if isinstance(result, dict):
        metrics.record_ingest(result.get("status"))
        notice = format_ingest_notice(result)
        if notice:
            await _safe_reply(message, notice, disable_web_page_preview=True)


HELPER_COMMANDS: set[str] = {
    "helper", "addhelper", "starthelper", "stophelper", "resethelperprogress",
    "startfwcatchbotvd", "addnewbot",
}
for _, (_, starts, resumes) in SOURCES.items():
    HELPER_COMMANDS.update(cmd.lstrip("/") for cmd in (*starts, *resumes))
for key in FORWARD_SOURCES:
    HELPER_COMMANDS.update({
        f"startfw{key}bot", f"startfw{key}",
        f"resumefw{key}bot", f"resumefw{key}",
    })


@router.message(Command(*sorted(HELPER_COMMANDS)))
async def helper_commands(message: Message):
    if not await has_admin_access(message):
        return
    await helper_manager.handle_command(message)


@router.message(
    F.chat.id == settings.adding_chat_id,
    F.text.regexp(r"^/[A-Za-z0-9_]+(?:@[A-Za-z0-9_]+)?(?:\s|$)")
)
async def dynamic_helper_commands(message: Message):
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
    await ensure_auth_indexes()
    await ensure_registry_indexes()
    registered_bots = await load_registry()
    log.info("Dynamic helper bot registry loaded: %s bots", registered_bots)
    await helper_userbot.start()
    helper_manager.bind()

    bot_session = None
    if settings.bot_api_base_url:
        api = TelegramAPIServer.from_base(
            settings.bot_api_base_url,
            is_local=settings.bot_api_is_local,
        )
        bot_session = AiohttpSession(
            api=api,
            limit=settings.bot_api_session_limit,
        )

    bot = Bot(
        settings.bot_token,
        session=bot_session,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )
    dp = Dispatcher()
    dp.include_router(router)

    app = web.Application()
    app.router.add_get(
        "/healthz",
        lambda _: web.json_response({
            "ok": True,
            "service": "unified-adding-helper",
            "mode": "webhook" if webhook else "polling",
            "adding": "only",
        }),
    )

    if webhook:
        path = settings.webhook_path if settings.webhook_path.startswith("/") else f"/{settings.webhook_path}"
        SimpleRequestHandler(
            dispatcher=dp,
            bot=bot,
            secret_token=settings.webhook_secret,
        ).register(app, path=path)
        setup_application(app, dp, bot=bot)
        runner = web.AppRunner(app)
        await runner.setup()
        await web.TCPSite(runner, settings.host, settings.port).start()
        await bot.set_webhook(
            settings.public_url + path,
            secret_token=settings.webhook_secret,
            drop_pending_updates=True,
        )
        log.info("Adding-only webhook ready: %s%s", settings.public_url, path)
        try:
            await asyncio.Event().wait()
        finally:
            await helper_userbot.stop()
            await cleanup(bot)
            await runner.cleanup()
    else:
        await bot.delete_webhook(drop_pending_updates=True)
        runner = web.AppRunner(app)
        await runner.setup()
        await web.TCPSite(runner, settings.host, settings.port).start()
        log.info("Adding-only polling ready")
        try:
            await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
        finally:
            await helper_userbot.stop()
            await cleanup(bot)
            await runner.cleanup()


if __name__ == "__main__":
    asyncio.run(run())
