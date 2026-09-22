from __future__ import annotations

import asyncio
import io
import logging

from aiogram import Bot
from aiogram.types import Message

from unified.parser import extract_name
from unified.store import save_character
from services.hash_service import hash_photo, hash_video
from services.source_resolver import resolve_source_collection, output_command_from_message

log = logging.getLogger(__name__)

async def ingest_message(bot: Bot, message: Message):
    target = message.reply_to_message or message
    name = extract_name(getattr(target, "caption", None) or getattr(target, "text", None))
    if not name:
        log.info("adding ingest skipped: name not parsed message=%s", message.message_id)
        return False

    media = None
    media_type = None
    for attr, typ in (("photo","photo"),("video","video"),("animation","video"),("document",None)):
        obj=getattr(target,attr,None)
        if not obj: continue
        if attr=="document":
            mime=str(getattr(obj,"mime_type","") or "").lower()
            fname=str(getattr(obj,"file_name","") or "").lower()
            if mime.startswith("image/") or fname.endswith((".jpg",".jpeg",".png",".webp",".gif")): typ="photo"
            elif mime.startswith("video/") or fname.endswith((".mp4",".mkv",".mov",".webm")): typ="video"
        if typ:
            media=obj; media_type=typ; break
    if not media: return False

    source_key=resolve_source_collection(target) or "unknown"
    command=output_command_from_message(target,None) or {
        "items_character_catcher":"/catch","items_characters_hallow":"/hallow","items_capture_character":"/capture",
        "items_character_seizer":"/seize","items_husbando_grabber":"/grab","items_grab_your_waifu":"/grab",
        "items_grab_your_husbando":"/grab","items_takers_character":"/take","items_catch_your_husbando":"/guess",
        "items_smash_character":"/smash","items_waifux_grab":"/grab","items_catch_your_waifu":"/guess",
        "items_waifu_grabber":"/grab","items_roronoa_zoro":"/challenge","items_character_picker":"/pick",
        "items_senpai_catcher":"/pick","items_bika_character":"/bika","items_super_zeko":"/ziceko",
        "items_orinx_waifu":"/orin","items_immortal_donghua":"/dao",
    }.get(source_key,"/name")

    try:
        result=await asyncio.wait_for(bot.download(getattr(media,"file_id","")),timeout=30)
        if isinstance(result,io.BytesIO): data=result.getvalue()
        elif hasattr(result,"read"): data=result.read()
        else: return False
        h=await asyncio.to_thread(hash_photo if media_type=="photo" else hash_video,data)
        origin=None
        origin_obj=getattr(target,"forward_origin",None)
        chat=getattr(origin_obj,"chat",None) or getattr(origin_obj,"sender_chat",None)
        mid=getattr(origin_obj,"message_id",None)
        if chat and mid is not None: origin=(int(chat.id),int(mid))
        await save_character(name=name,command=command,source_key=source_key,media_type=media_type,
                             file_unique_id=str(getattr(media,"file_unique_id","") or ""),media_hash=h,source_origin=origin,
                             archive=(message.chat.id,message.message_id))
        return True
    except Exception:
        log.exception("ingest failed")
        return False
