from __future__ import annotations

import asyncio
import logging
import signal
import sys
from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandObject
from aiogram.types import Message
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application

from unified.config import settings
from unified.store import ensure_indexes, close, characters
from unified.ingest import ingest_message
from unified.lookup import lookup_message
from services.result_formatter import result_buttons
from utils.text import h, first_token

sys.path.insert(0, "namebotv3")

from helper.controller import HelperController
from helper.runtime import HelperRuntime

logging.basicConfig(level=getattr(logging,settings.log_level,logging.INFO),
                    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s")
log=logging.getLogger("unified")

router=Router()
controller=HelperController()
runtime=HelperRuntime()

def owner(m:Message)->bool:
    return bool(m.from_user and m.from_user.id in settings.owner_ids)

def format_result(doc:dict)->str:
    name=h(doc.get("name",""))
    command=h(doc.get("command") or "/name")
    cmd=doc.get("command") or "/name"
    first=h(first_token(doc.get("name","")))
    full=h(doc.get("name",""))
    return (f"<b>NAME :</b> <code>{name}</code>\n"
            f"────────────────\n"
            f"🔹 <b>Hint :</b> <code>{command} {first}</code>\n"
            f"🔸 <b>Full :</b> <code>{command} {full}</code>\n\n"
            f"Powered by <b>Bika</b>")

async def start_source(key:str):
    if not runtime.client: return False
    await controller.start(key,1,runtime.client,settings.helper_target_chat or settings.adding_chat_id)
    return True

@router.message(Command("startdmcatchbot"))
async def start_catch(m:Message):
    if owner(m): await start_source("catch") and m.reply("ok")
@router.message(Command("startdmgrabbot"))
async def start_grab(m:Message):
    if owner(m): await start_source("grab") and m.reply("ok")
@router.message(Command("startdmsenpaibot"))
async def start_senpai(m:Message):
    if owner(m): await start_source("senpai") and m.reply("ok")
@router.message(Command("startdmhallowbot"))
async def start_hallow(m:Message):
    if owner(m): await start_source("hallow") and m.reply("ok")
@router.message(Command("startdmtakersbot"))
async def start_takers(m:Message):
    if owner(m): await start_source("takers") and m.reply("ok")
@router.message(Command("stopdm"))
async def stop_dm(m:Message):
    if owner(m):
        await controller.stop_all_dm()
        await m.reply("✅ Adding workers stopped.")

@router.message(F.func(lambda m: bool(getattr(m.chat,"id",0)==settings.adding_chat_id) and bool(getattr(m,"photo",None) or getattr(m,"video",None) or getattr(m,"animation",None) or getattr(m,"document",None))))
async def adding_ingest(m:Message):
    if settings.adding_chat_id and m.chat.id==settings.adding_chat_id:
        ok=await ingest_message(m.bot,m)
        if ok: log.info("INGESTED message=%s",m.message_id)

@router.message(F.func(lambda m: bool(getattr(m.chat,"id",0)!=settings.adding_chat_id) and bool(getattr(m,"photo",None) or getattr(m,"video",None) or getattr(m,"animation",None) or getattr(m,"document",None))))
async def lookup_media(m:Message):
    if m.chat.type=="private" and not settings.lookup_in_private: return
    if m.chat.type!="private" and not settings.lookup_in_groups: return
    doc,reason=await lookup_message(m.bot,m)
    if doc:
        await m.reply(format_result(doc),disable_web_page_preview=True,reply_markup=result_buttons(type("X",(),{"command":doc.get("command","/name"),"name":doc.get("name","")})()))
    elif settings.reply_not_found:
        await m.reply("❌ Character not found.")

@router.message(Command("stats"))
async def stats(m:Message):
    if not owner(m): return
    count=await characters.count_documents({})
    await m.reply(f"📊 Unified DB\nCharacters: {count}\nDB: {settings.db_name}")

async def run():
    if not settings.bot_token: raise RuntimeError("BOT_TOKEN is required")
    if not settings.mongo_uri: raise RuntimeError("MONGO_URI is required")
    if not settings.owner_ids: raise RuntimeError("OWNER_IDS is required")
    if not settings.adding_chat_id: raise RuntimeError("ADDING_CHAT_ID is required")

    await ensure_indexes()
    bot=Bot(settings.bot_token,default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    dp=Dispatcher(); dp.include_router(router)

    if settings.api_id and settings.api_hash and settings.session_string:
        await runtime.start(controller)
        log.info("Helper userbot started")
    else:
        log.warning("Helper disabled: API_ID/API_HASH/SESSION_STRING missing")

    if settings.use_webhook or settings.public_url:
        path=settings.webhook_path if settings.webhook_path.startswith("/") else "/"+settings.webhook_path
        app=web.Application()
        app.router.add_get("/healthz",lambda _: web.json_response({"ok":True,"db":settings.db_name}))
        SimpleRequestHandler(dispatcher=dp,bot=bot,secret_token=settings.webhook_secret).register(app,path=path)
        setup_application(app,dp,bot=bot)
        runner=web.AppRunner(app); await runner.setup(); site=web.TCPSite(runner,settings.host,settings.port); await site.start()
        await bot.set_webhook(settings.public_url+path,secret_token=settings.webhook_secret,drop_pending_updates=True)
        try:
            await asyncio.Event().wait()
        finally:
            await runtime.stop(); await controller.stop_all_dm(); await close(); await bot.session.close(); await runner.cleanup()
    else:
        try:
            await dp.start_polling(bot,allowed_updates=dp.resolve_used_update_types())
        finally:
            await runtime.stop(); await controller.stop_all_dm(); await close(); await bot.session.close()

if __name__=="__main__":
    asyncio.run(run())
