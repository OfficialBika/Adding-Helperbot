from __future__ import annotations

import asyncio
import logging
import sys
from pathlib import Path

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
from unified.ingest import ingest_message
from unified.lookup import lookup_message
from helper.runtime import HelperUserbot
from helper.manager import HelperManager
from services.result_formatter import result_buttons
from utils.text import h, first_token

logging.basicConfig(
    level=getattr(logging, settings.log_level, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
log = logging.getLogger("unified")

router = Router(name="unified")
helper_userbot = HelperUserbot()
helper_manager = HelperManager(helper_userbot)


def owner(message: Message) -> bool:
    return bool(message.from_user and message.from_user.id in settings.owner_ids)


def is_media(message: Message) -> bool:
    return bool(
        getattr(message, "photo", None)
        or getattr(message, "video", None)
        or getattr(message, "animation", None)
        or getattr(message, "document", None)
    )


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


@router.message(Command("start"))
async def start(message: Message):
    if not owner(message):
        return
    await message.reply(
        "🤖 <b>Adding & Helper Main</b>\n\n"
        "Adding: <code>ONLINE</code>\n"
        "Helper: <code>ONLINE</code>\n\n"
        "Use /status for system status.\n"
        "Use /helper for Helper controls."
    )


@router.message(Command("status"))
async def status(message: Message):
    if not owner(message):
        return
    helper = await helper_manager.status_text()
    count = await characters.count_documents({})
    helper_state = "ONLINE" if helper_userbot.client else "OFFLINE"
    await message.reply(
        f"🛠 <b>ADDING BOT STATUS</b>\n"
        f"Characters: <code>{count}</code>\n"
        f"Adding Group: <code>{settings.adding_chat_id}</code>\n"
        f"Helper Userbot: <code>{helper_state}</code>\n\n"
        f"{helper}"
    )


@router.message(Command("stats"))
async def stats(message: Message):
    if not owner(message):
        return
    count = await characters.count_documents({})
    await message.reply(
        f"📊 <b>Unified Adding + Lookup</b>\n"
        f"Characters: <code>{count}</code>\n"
        f"DB: <code>{h(settings.db_name)}</code>\n"
        f"Adding Group: <code>{settings.adding_chat_id}</code>\n"
        "Mode: <code>forward-only adding</code>"
    )


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


@router.message(F.chat.id == settings.adding_chat_id, F.func(is_media))
async def adding_ingest(message: Message):
    # Adding is intentionally restricted to forwarded channel/source posts.
    # Ordinary media sent directly into the Adding group is ignored.
    is_forwarded = bool(getattr(message, "forward_origin", None) or getattr(message, "forward_from_chat", None))
    helper_user_id = helper_userbot.user_id
    is_helper_inline = bool(helper_user_id and getattr(message.from_user, "id", None) == helper_user_id)
    if not is_forwarded and not is_helper_inline:
        return
    trusted_helpers = {helper_userbot.user_id} if helper_userbot.user_id else set()
    ok = await ingest_message(message.bot, message, trusted_user_ids=trusted_helpers)
    if ok:
        log.info("INGESTED forwarded post message=%s chat=%s", message.message_id, message.chat.id)


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

    doc, reason = await lookup_message(message.bot, message)
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


HELPER_COMMANDS = [
    "helper", "addhelper", "helperstatus", "addhelperstatus", "stophelper",
    "resethelperprogress", "startcatchbot", "resumecatchbot",
    "startcatcherbot", "resumecatcherbot", "starthallowbot", "resumehallowbot",
    "startcapturebot", "resumecapturebot", "startseizerbot", "resumeseizerbot",
    "startgrabbot", "resumegrabbot", "starttakersbot", "resumetakersbot",
    "startpickerbot", "resumepickerbot", "startzicekobot", "resumezicekobot",
    "startorinbot", "resumeorinbot", "startdaobot", "resumedaobot",
    "startbika", "resumebika", "startsenpaibot", "resumesenpaibot",
    "startsmashbot", "resumesmashbot", "startwaifuxgrabbot", "resumewaifuxgrabbot",
    "startwaifugrabberbot", "resumewaifugrabberbot", "startcatchyourwaifubot",
    "resumecatchyourwaifubot", "startcatchyourhusbandobot", "resumecatchyourhusbandobot",
]


@router.message(Command(*HELPER_COMMANDS))
async def helper_commands(message: Message):
    if not owner(message):
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
    await helper_userbot.start()
    helper_manager.bind()

    bot = Bot(
        settings.bot_token,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )
    dp = Dispatcher()
    dp.include_router(router)

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
        log.info("Polling ready; Adding mode=forward-only")
        try:
            await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
        finally:
            await helper_userbot.stop()
            await cleanup(bot)
            await runner.cleanup()


if __name__ == "__main__":
    asyncio.run(run())
