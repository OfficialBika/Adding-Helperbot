from __future__ import annotations

import asyncio
import io
import logging
import time

from aiogram import Bot
from aiogram.types import Message

from unified.config import settings
from unified.store import characters, _chunks
from unified.parser import clean_name
from services.hash_service import hash_photo, hash_video, hamming_hex
from utils.media import extract_media
from services.source_resolver import resolve_lookup_scope, output_command_from_message

log = logging.getLogger(__name__)

def _scope(message: Message) -> list[str] | None:
    scope = resolve_lookup_scope(message)
    return scope.collections

def _cmd(message: Message, source_key: str | None, fallback: str = "/name") -> str:
    return output_command_from_message(message, None) or ("/name" if not source_key else {
        "items_character_catcher":"/catch","items_characters_hallow":"/hallow","items_capture_character":"/capture",
        "items_character_seizer":"/seize","items_husbando_grabber":"/grab","items_grab_your_waifu":"/grab",
        "items_grab_your_husbando":"/grab","items_takers_character":"/take","items_catch_your_husbando":"/guess",
        "items_smash_character":"/smash","items_waifux_grab":"/grab","items_catch_your_waifu":"/guess",
        "items_waifu_grabber":"/grab","items_roronoa_zoro":"/challenge","items_character_picker":"/pick",
        "items_senpai_catcher":"/pick","items_bika_character":"/bika","items_super_zeko":"/ziceko",
        "items_orinx_waifu":"/orin","items_immortal_donghua":"/dao",
    }.get(source_key, fallback))

async def _download(bot: Bot, file_id: str) -> bytes | None:
    try:
        result = await asyncio.wait_for(bot.download(file_id), timeout=20)
        if isinstance(result, io.BytesIO): return result.getvalue()
        if hasattr(result, "read"):
            value = result.read()
            return value if isinstance(value, bytes) else bytes(value)
    except Exception as exc:
        log.info("media download failed: %s", exc)
    return None

async def _find_exact(file_uid: str, sha: str | None, origin, scope):
    ors = []
    if file_uid: ors += [{"file_unique_ids": file_uid}]
    if sha: ors += [{"sha256": sha}, {"sha256_aliases": sha}]
    if origin: ors += [{"source_origin.chat_id": origin[0], "source_origin.message_id": origin[1]}]
    if not ors: return None
    query = {"$or": ors}
    if scope: query["source_key"] = {"$in": scope}
    return await characters.find_one(query)

def _similarity(query_hash, item) -> float:
    metrics=[]
    for a,b,w in ((query_hash.phash,item.get("phash"),.35),(query_hash.dhash,item.get("dhash"),.25),
                  (query_hash.whash,item.get("whash"),.15),(query_hash.phash_large,item.get("phash_large"),.15),
                  (query_hash.colorhash,item.get("colorhash"),.10)):
        d=hamming_hex(a,b)
        if d is not None: metrics.append((max(0,1-d/max(1,len(str(a))*4)),w))
    return sum(s*w for s,w in metrics)/sum(w for _,w in metrics) if metrics else 0.0

async def lookup_message(bot: Bot, message: Message):
    media=extract_media(message)
    if not media: return None, "no_media"
    scope=_scope(media.source_message)
    output_hint=output_command_from_message(media.source_message, None)
    uid=str(getattr(media.obj,"file_unique_id","") or "")
    origin=None
    try:
        origin_obj=getattr(media.source_message,"forward_origin",None)
        chat=getattr(origin_obj,"chat",None) or getattr(origin_obj,"sender_chat",None)
        mid=getattr(origin_obj,"message_id",None)
        if chat and mid is not None: origin=(int(chat.id),int(mid))
    except Exception: pass

    # Fast exact lookup before downloading.
    doc=await _find_exact(uid,None,origin,scope)
    if doc: return doc,"uid/origin"

    data=await _download(bot,str(getattr(media.obj,"file_id","") or ""))
    if not data: return None,"download_failed"
    h=await asyncio.to_thread(hash_photo if media.media_type=="photo" else hash_video,data)

    doc=await _find_exact(uid,h.sha256,origin,scope)
    if doc: return doc,"exact"

    # Approximate photo lookup: query by pHash/dHash chunks, then score in Python.
    chunks=set(_chunks(h.phash)) | set(_chunks(h.dhash))
    if media.media_type=="photo" and chunks:
        ors=[{"phash_chunks": {"$in":[c]}} for c in chunks] + [{"dhash_chunks":{"$in":[c]}} for c in chunks]
        q={"$or":ors}
        if scope: q["source_key"]={"$in":scope}
        cursor=characters.find(q).limit(2500)
        best=None; best_score=0.0
        async for item in cursor:
            score=_similarity(h,item)
            p=hamming_hex(h.phash,item.get("phash")); d=hamming_hex(h.dhash,item.get("dhash"))
            if (p is not None and p <= settings.photo_threshold) or (d is not None and d <= settings.dhash_threshold):
                if score>.80 and score>best_score: best,best_score=item,score
        if best: return best,"photo_similarity"

    if media.media_type=="video":
        if h.video_signature:
            doc=await characters.find_one({"video_signature":h.video_signature, **({"source_key":{"$in":scope}} if scope else {})})
            if doc: return doc,"video_signature"
        if h.duration_ms:
            q={"media_type":"video","duration_bucket":{"$gte":max(0,round(h.duration_ms/1000)-4)," $lte":round(h.duration_ms/1000)+4}}
            if scope: q["source_key"]={"$in":scope}
            cursor=characters.find(q).limit(5000)
            best=None; best_avg=999
            async for item in cursor:
                distances=[]
                bypos={round(float(s.get("position",0)),3):s for s in item.get("video_samples",[])}
                for s in h.video_samples:
                    other=bypos.get(round(float(s.position),3))
                    if other:
                        for a,b in ((s.phash,other.get("phash")),(s.dhash,other.get("dhash"))):
                            d=hamming_hex(a,b)
                            if d is not None: distances.append(d)
                if distances:
                    avg=sum(distances)/len(distances); mn=min(distances)
                    if mn<=settings.video_frame_threshold and avg<=settings.video_avg_threshold and avg<best_avg:
                        best,best_avg=item,avg
            if best: return best,"video_similarity"
    return None,"not_found"
