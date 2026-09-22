from __future__ import annotations

import asyncio
import logging
import sys
from pathlib import Path

# Reuse the proven media hashing/source-resolution modules from NameBot V3.
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "namebotv3"))
sys.path.insert(0, str(ROOT))

from aiohttp import web
from aiogram import Dispatcher, F, Router, Bot
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command
from aiogram.types import Message
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application

from unified.config import settings
from unified.store import ensure_indexes, close, characters
from unified.ingest import ingest_message
from unified.lookup import lookup_message
from services.result_formatter import result_buttons
from utils.text import h, first_token

from helper.controller import HelperController
from helper.runtime import HelperRuntime

logging.basicConfig(
    level=getattr(logging, settings.log_level, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
log = logging.getLogger("unified")

router = Router(name="unified")
controller = HelperController()
runtime = HelperRuntime()

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
    raw_name = str(doc.get("name") or "")
    command = str(doc.get("command") or "/name")
    name = h(raw_name)
    hint = h(f"{command} {first_token(raw_name)}")
    full = h(f"{command} {raw_name}")
    return (
        f"<b>NAME :</b> <code>{name}</code>\n"
        "────────────────\n"
        f"🔹 <b>Hint :</b> <code>{hint}</code>\n"
        f"🔸 <b>Full :</b> <code>{full}</code>\n\n"
        "Powered by <b>Bika</b>"
    )

async def start_source(message: Message, key: str) -> None:
    if not runtime.client:
        await message.reply("⚠️ Adding helper userbot is not connected.")
        return
    await controller.start(
        key,
        1,
        runtime.client,
        settings.helper_target_chat or settings.adding_chat_id,
    )
    await message.reply(f"✅ Adding worker started: <code>{key}</code>")

@router.message(Command("startdmcatchbot"))
async def start_catch(message: Message):
    if owner(message): await start_source(message, "catch")

@router.message(Command("startdmgrabbot"))
async def start_grab(message: Message):
    if owner(message): await start_source(message, "grab")

@router.message(Command("startdmsenpaibot"))
async def start_senpai(message: Message):
    if owner(message): await start_source(message, "senpai")

@router.message(Command("startdmhallowbot"))
async def start_hallow(message: Message):
    if owner(message): await start_source(message, "hallow")

@router.message(Command("startdmtakersbot"))
async def start_takers(message: Message):
    if owner(message): await start_source(message, "takers")

@router.message(Command("stopdm"))
async def stop_dm(message: Message):
    if not owner(message): return
    await controller.stop_all_dm()
    await message.reply("✅ All Adding workers stopped.")

@router.message(Command("addingstatus"))
async def adding_status(message: Message):
    if not owner(message): return
    keys = ("catch", "grab", "senpai", "hallow", "takers")
    lines = [f"{key}: {'RUNNING' if controller.is_running(key) else 'STOPPED'}" for key in keys]
    await message.reply("📥 <b>Adding status</b>\n" + "\n".join(lines))

@router.message(Command("stats"))
async def stats(message: Message):
    if not owner(message): return
    count = await characters.count_documents({})
    await message.reply(
        f"📊 <b>Unified Adding + Lookup</b>\n"
        f"Characters: <code>{count}</code>\n"
        f"DB: <code>{h(settings.db_name)}</code>\n"
        f"Adding Group: <code>{settings.adding_chat_id}</code>"
    )

@router.message(F.chat.id == settings.adding_chat_id, F.func(is_media))
async def adding_ingest(message: Message):
    # The Adding group is ingestion-only. It never performs lookup.
    ok = await ingest_message(message.bot, message)
    if ok:
        log.info("INGESTED message=%s chat=%s", message.message_id, message.chat.id)

@router.message(F.func(lambda m: bool(getattr(m.chat, "id", 0) != settings.adding_chat_id)), F.func(is_media))
async def lookup_media(message: Message):
    if message.chat.type == "private" and not settings.lookup_in_private:
        return
    if message.chat.type != "private" and not settings.lookup_in_groups:
        return

    doc, reason = await lookup_message(message.bot, message)
    if doc:
        await message.reply(
            format_result(doc),
            disable_web_page_preview=True,
            reply_markup=result_buttons(
                type("LookupItem", (), {
                    "command": doc.get("command", "/name"),
                    "name": doc.get("name", ""),
                })()
            ),
        )
    elif settings.reply_not_found:
        await message.reply("❌ Character not found.")

async def run():
    if not settings.bot_token: raise RuntimeError("BOT_TOKEN is required")
    if not settings.mongo_uri: raise RuntimeError("MONGO_URI is required")
    if not settings.owner_ids: raise RuntimeError("OWNER_IDS is required")
    if not settings.adding_chat_id: raise RuntimeError("ADDING_CHAT_ID is required")

    await ensure_indexes()
    bot = Bot(
        settings.bot_token,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )
    dp = Dispatcher()
    dp.include_router(router)

    if settings.api_id and settings.api_hash and settings.session_string:
        await runtime.start(controller)
        log.info("Adding helper userbot started")
    else:
        log.warning("Adding helper disabled: API_ID/API_HASH/SESSION_STRING missing")

    webhook = settings.use_webhook or bool(settings.public_url)
    if webhook:
        path = settings.webhook_path if settings.webhook_path.startswith("/") else "/" + settings.webhook_path
        app = web.Application()
        app.router.add_get(
            "/healthz",
            lambda _: web.json_response({
                "ok": True,
                "service": "unified-adding-lookup",
                "db": settings.db_name,
                "adding_chat_id": settings.adding_chat_id,
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

        if not settings.public_url:
            raise RuntimeError("PUBLIC_URL is required in webhook mode")
        await bot.set_webhook(
            settings.public_url + path,
            secret_token=settings.webhook_secret,
            drop_pending_updates=True,
        )
        log.info("Unified webhook ready on %s%s", settings.public_url, path)

        try:
            await asyncio.Event().wait()
        finally:
            await runtime.stop()
            await controller.stop_all_dm()
            await close()
            await bot.session.close()
            await runner.cleanup()
    else:
        try:
            await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
        finally:
            await runtime.stop()
            await controller.stop_all_dm()
            await close()
            await bot.session.close()

if __name__ == "__main__":
    asyncio.run(run())
