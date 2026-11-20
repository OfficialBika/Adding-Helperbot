from __future__ import annotations

import asyncio
import re
import secrets
from datetime import datetime, timedelta, timezone
from typing import Any

from aiogram import Router
from aiogram.dispatcher.event.bases import SkipHandler
from aiogram.filters import Command
from aiogram.types import Message

from unified.store import db, characters
from config import settings, BOT_SOURCE_COLLECTION

router = Router(name="dynamic_source_registry")
REGISTRY_KEY = "dynamic_source_registry_v1"
PENDING_PREFIX = "dynamic_source_pending:"
KEY_RE = re.compile(r"^[a-z][a-z0-9_]{1,47}$")
USERNAME_RE = re.compile(r"^@[A-Za-z0-9_]{5,32}$")
COMMAND_RE = re.compile(r"^/[a-z][a-z0-9_]{1,31}$")
VALID_MODES = {"inline", "forward", "both", "dm", "manual"}
VALID_PARSERS = {"builtin", "generic"}
VALID_COLLECTIONS = frozenset({
    "items_character_catcher", "items_character_catcher_fw",
    "items_characters_hallow", "items_capture_character",
    "items_character_seizer", "items_husbando_grabber",
    "items_grab_your_waifu", "items_grab_your_husbando",
    "items_takers_character", "items_catch_your_husbando",
    "items_smash_character", "items_waifux_grab",
    "items_catch_your_waifu", "items_waifu_grabber",
    "items_roronoa_zoro", "items_character_picker",
    "items_bika_character", "items_senpai_catcher",
    "items_super_zeko", "items_orinx_waifu",
    "items_immortal_donghua", "items_kairo_character",
    "items_grabber_fw",
})
_REGISTRY: list[dict[str, Any]] = []

def _now() -> datetime:
    return datetime.now(timezone.utc)

def _username(value: str) -> str:
    value = str(value or "").strip()
    if not value or value == "-":
        return ""
    if not value.startswith("@"):
        value = "@" + value
    return value.lower()

def _source_key(value: str) -> str:
    value = str(value or "").strip().lower()
    return value if KEY_RE.fullmatch(value) else ""

def _command(value: str) -> str:
    value = str(value or "").strip().lower()
    return value if COMMAND_RE.fullmatch(value) else ""

def _owner_dm(message: Message) -> bool:
    return bool(message.chat.type == "private" and message.from_user and message.from_user.id in settings.owner_ids)

def _escape(value: Any) -> str:
    from html import escape
    return escape(str(value if value is not None else "-"))

async def get_registered_sources(*, active_only: bool = True) -> list[dict[str, Any]]:
    doc = await db.settings.find_one({"key": REGISTRY_KEY}, {"sources": 1})
    sources = list((doc or {}).get("sources") or [])
    return [dict(x) for x in sources if x.get("enabled", True)] if active_only else [dict(x) for x in sources]

async def ensure_registry_indexes() -> None:
    # Separate collection-level index for owner wizard sessions; does not
    # touch the character collection or its identity indexes.
    await db.settings.create_index(
        [("key", 1)],
        name="uq_settings_dynamic_source_key",
        unique=True,
        partialFilterExpression={"key": {"$in": [REGISTRY_KEY]}},
        background=True,
    )

def get_registered_sources_cached(*, active_only: bool = True) -> list[dict[str, Any]]:
    return [dict(x) for x in _REGISTRY if (x.get("enabled", True) or not active_only)]

def find_dynamic_source_by_key(source_key: str) -> dict[str, Any] | None:
    key = str(source_key or "").strip().lower()
    for item in _REGISTRY:
        if item.get("enabled", True) and item.get("source_key") == key:
            return dict(item)
    return None

def find_dynamic_source_for_message(message: Any) -> dict[str, Any] | None:
    origin = getattr(message, "forward_origin", None)
    chat = (getattr(origin, "chat", None) or getattr(origin, "sender_chat", None)) if origin else None
    if chat is None:
        chat = getattr(message, "forward_from_chat", None)
    chat_username = _username(getattr(chat, "username", "") or "") if chat else ""
    chat_id = str(getattr(chat, "id", "") or "") if chat else ""
    sender = getattr(origin, "sender_user", None) if origin else None
    sender = sender or getattr(message, "forward_from", None) or getattr(message, "via_bot", None)
    if sender is None and getattr(getattr(message, "from_user", None), "is_bot", False):
        sender = message.from_user
    sender_username = _username(getattr(sender, "username", "") or "") if sender else ""
    sender_id = str(getattr(sender, "id", "") or "") if sender else ""
    for item in _REGISTRY:
        if not item.get("enabled", True):
            continue
        if chat_username and item.get("forward_source") == chat_username:
            return dict(item)
        if chat_id and item.get("forward_source") == chat_id:
            return dict(item)
        if sender_username and item.get("bot_username") == sender_username:
            return dict(item)
        if sender_id and str(item.get("bot_user_id") or "") == sender_id:
            return dict(item)
    return None

def parse_dynamic_text(source: dict[str, Any] | None, text: str) -> dict[str, str]:
    if not source or source.get("parser_type") != "generic":
        return {}
    rules = source.get("parser_rules") or {}
    labels = {"name": str(rules.get("name_label") or "Name"), "id": str(rules.get("id_label") or "ID")}
    found: dict[str, str] = {}
    for line in str(text or "").replace("\r", "\n").splitlines():
        for field, label in labels.items():
            if field in found or not label:
                continue
            match = re.match(r"^[^A-Za-z0-9]*" + re.escape(label) + r"\s*[:：=\-]\s*(.*?)\s*$", line.strip(), re.I)
            if match and match.group(1).strip():
                found[field] = match.group(1).strip().strip("`")[:180]
    return found

def install_dynamic_source_registry(sources: list[dict[str, Any]]) -> None:
    global _REGISTRY
    next_registry = [dict(x) for x in sources if x.get("enabled", True)]
    # Resolve a full next mapping first. Preserve the last good snapshot if the
    # resolver cannot install it, so registry data and source authorization do
    # not drift into a partially refreshed state.
    try:
        from services.source_resolver import install_dynamic_source_registry as install
        install(next_registry)
    except Exception:
        import logging
        logging.getLogger(__name__).exception("Dynamic source resolver refresh failed; retaining previous registry snapshot")
        raise
    _REGISTRY = next_registry

async def refresh_dynamic_source_registry() -> int:
    await ensure_registry_indexes()
    sources = await get_registered_sources(active_only=True)
    install_dynamic_source_registry(sources)
    return len(sources)

async def dynamic_source_refresh_loop(interval: float = 15.0) -> None:
    while True:
        try:
            await asyncio.sleep(max(5.0, interval))
            await refresh_dynamic_source_registry()
        except asyncio.CancelledError:
            raise
        except Exception:
            import logging
            logging.getLogger(__name__).exception("Dynamic source refresh failed; retaining last good cache")

def _static_key(key: str) -> bool:
    return key in set(BOT_SOURCE_COLLECTION.values()) or key in VALID_COLLECTIONS

async def _source_key_status(key: str) -> tuple[str, str]:
    existing = await db.settings.find_one({"key": REGISTRY_KEY, "sources.source_key": key}, {"sources.$": 1})
    if existing and existing.get("sources"):
        return "EXISTS", "registered source key"
    if _static_key(key):
        return "EXISTS", "built-in source key"
    record = await characters.find_one({"source_key": key}, {"_id": 1})
    if record:
        return "EXISTS", "existing character records"
    return "NEW", "no source key or character records found"

async def _pending(owner_id: int) -> dict[str, Any] | None:
    doc = await db.settings.find_one({"key": f"{PENDING_PREFIX}{int(owner_id)}"})
    if not doc:
        return None
    expiry = doc.get("expires_at")
    if expiry and expiry < _now():
        await db.settings.delete_one({"_id": doc["_id"]})
        return None
    return doc

async def _save_pending(owner_id: int, draft: dict[str, Any], step: str) -> None:
    await db.settings.update_one({"key": f"{PENDING_PREFIX}{int(owner_id)}"}, {"$set": {"owner_id": int(owner_id), "draft": draft, "step": step, "expires_at": _now() + timedelta(minutes=15)}}, upsert=True)

async def _clear_pending(owner_id: int) -> None:
    await db.settings.delete_one({"key": f"{PENDING_PREFIX}{int(owner_id)}"})

def _preview(draft: dict[str, Any]) -> str:
    return "\n".join([
        "🧩 <b>SOURCE BOT REGISTRATION PREVIEW</b>",
        "",
        f"Source key: <b>{_escape(draft.get('source_status'))}</b> ({_escape(draft.get('source_status_reason'))})",
        f"Bot: <code>{_escape(draft.get('name'))}</code> / <code>{_escape(draft.get('bot_username'))}</code>",
        f"Source key: <code>{_escape(draft.get('source_key'))}</code>",
        "Mongo character collection: <code>characters</code>",
        f"Output command: <code>{_escape(draft.get('output_command'))}</code>",
        f"Mode: <code>{_escape(draft.get('mode'))}</code>",
        f"Forward source: <code>{_escape(draft.get('forward_source'))}</code>",
        f"DM command: <code>{_escape(draft.get('dm_command'))}</code>",
        f"Parser: <code>{_escape(draft.get('parser_type'))}</code> / <code>{_escape(draft.get('parser_rules'))}</code>",
        "",
        "Correct: /confirm",
        "Cancel: /cancel",
    ])

async def _ask(message: Message, step: str) -> None:
    prompts = {
        "name": "Bot display name ထည့်ပါ။",
        "username": "Bot username ထည့်ပါ။ ဥပမာ @NewSourceBot (မရှိလျှင် -)",
        "source_key": "Source Key ထည့်ပါ။ ဥပမာ items_new_source",
        "reuse": "ဒီ Source Key ရှိပြီးသားပါ။ ရှိပြီးသားကို သုံးမယ်ဆို REUSE ပို့ပါ။",
        "output_command": "Lookup output command ထည့်ပါ။ ဥပမာ /name",
        "mode": "Mode: inline / forward / both / dm / manual",
        "forward_source": "Forward source username သို့မဟုတ် -100... ID ထည့်ပါ။ မရှိလျှင် -",
        "dm_command": "DM command template ထည့်ပါ။ ဥပမာ /check {id} (မရှိလျှင် -)",
        "dm_max_id": "ဒီ bot အတွက် စစ်ဆေးမယ့် အများဆုံး ID ထည့်ပါ။ ဥပမာ 10000 (အကန့်အသတ်မဲ့ မစစ်ပါ)",
        "dm_timeout": "Response timeout ကို စက္ကန့်ဖြင့် ထည့်ပါ (5-120)။ ဥပမာ 30",
        "dm_max_misses": "Auto-stop မတိုင်မီ ဆက်တိုက် no-response အများဆုံးအကြိမ် (1-100) ထည့်ပါ။ ဥပမာ 10",
        "parser": "Parser type: builtin / generic",
        "name_label": "Generic parser Name label ထည့်ပါ။ ဥပမာ Name",
        "id_label": "ID label ထည့်ပါ။ မရှိလျှင် -",
    }
    await message.answer(prompts[step] + "\n/cancel ဖြင့် ပယ်ဖျက်နိုင်ပါတယ်။")

async def _save_source(draft: dict[str, Any], owner_id: int) -> None:
    """Atomically validate and append a registration without mutating existing entries."""
    item = dict(draft)
    for field in ("source_status", "source_status_reason", "reuse_existing"):
        item.pop(field, None)
    item["source_key"] = _source_key(item.get("source_key"))
    item["bot_username"] = _username(item.get("bot_username"))
    item["output_command"] = _command(item.get("output_command"))
    if not item["source_key"] or not item["output_command"]:
        raise ValueError("Invalid source key or output command.")
    if item.get("mode") not in VALID_MODES:
        raise ValueError("Invalid source mode.")
    if item.get("mode") in {"inline", "both"} and not item.get("bot_username"):
        raise ValueError("Inline mode requires a bot username.")
    if item.get("mode") in {"forward", "both"} and not item.get("forward_source"):
        raise ValueError("Forward source is required for this mode.")
    if item.get("mode") == "dm":
        if not item.get("bot_username") or not item.get("dm_command"):
            raise ValueError("DM mode requires a bot username and command template.")
        if not 1 <= int(item.get("max_id") or 0) <= 10000000:
            raise ValueError("DM mode requires a finite max_id between 1 and 10,000,000.")
        if not 5 <= int(item.get("response_timeout") or 0) <= 120:
            raise ValueError("DM response timeout must be 5-120 seconds.")
        if not 1 <= int(item.get("max_no_response") or 0) <= 100:
            raise ValueError("DM max_no_response must be 1-100.")
    if item.get("dm_command") and (
        "{id}" not in item["dm_command"]
        or not re.fullmatch(r"/[A-Za-z0-9_ ]*\{id\}[A-Za-z0-9_ ]*", item["dm_command"])
    ):
        raise ValueError("Invalid DM command template.")
    if item.get("parser_type") == "generic":
        rules = item.get("parser_rules") or {}
        if not rules.get("name_label"):
            raise ValueError("Generic parser requires a name label.")
        item["parser_rules"] = {
            "name_label": str(rules["name_label"])[:40],
            "id_label": str(rules.get("id_label") or "ID")[:40],
        }
    now = _now()
    item.update({
        "enabled": True, "created_by": int(owner_id), "created_at": now,
        "updated_at": now, "version": 1, "registration_id": secrets.token_hex(8),
    })
    # Guard duplicate registration identity with a single atomic update against
    # the registry document. The document is created only when it is absent.
    registry = await db.settings.find_one({"key": REGISTRY_KEY}, {"_id": 1})
    if registry:
        query = {"_id": registry["_id"], "key": REGISTRY_KEY, "$nor": [
            {"sources.source_key": item["source_key"]},
            *([{"sources.bot_username": item["bot_username"]}] if item["bot_username"] else []),
            *([{"sources.forward_source": item.get("forward_source")}] if item.get("forward_source") else []),
        ]}
        result = await db.settings.update_one(
            query,
            {"$push": {"sources": item}, "$set": {"updated_at": now}},
        )
        if not result.modified_count:
            raise ValueError("Duplicate source key or bot identity; no registration was saved.")
    else:
        try:
            await db.settings.insert_one({
                "key": REGISTRY_KEY, "schema_version": 1,
                "sources": [item], "created_at": now, "updated_at": now,
            })
        except Exception as exc:
            raise ValueError("Registry was created concurrently; retry /confirm.") from exc
    await refresh_dynamic_source_registry()

@router.message(Command("addnewbot"))
async def addnewbot(message: Message) -> None:
    if not _owner_dm(message):
        return
    await _save_pending(message.from_user.id, {}, "name")
    await _ask(message, "name")

@router.message(Command("cancel"))
async def cancel_registration(message: Message) -> None:
    if not _owner_dm(message):
        return
    await _clear_pending(message.from_user.id)
    await message.answer("❌ Cancelled. No source registry changes were made.")

@router.message(Command("confirm"))
async def confirm_registration(message: Message) -> None:
    if not _owner_dm(message):
        return
    pending = await _pending(message.from_user.id)
    if not pending or pending.get("step") != "confirm":
        await message.answer("No valid preview. Use /addnewbot.")
        return
    draft = dict(pending.get("draft") or {})
    if draft.get("source_status") == "EXISTS" and not draft.get("reuse_existing"):
        await message.answer("Existing source requires REUSE. Registration was not saved.")
        return
    try:
        await _save_source(draft, message.from_user.id)
    except ValueError as exc:
        await message.answer(f"❌ {_escape(exc)}")
        return
    await _clear_pending(message.from_user.id)
    await message.answer("✅ Source registered. Adding and Lookup registry refresh automatically; existing records were not changed.")

@router.message(Command("listbots"))
async def listbots(message: Message) -> None:
    if not _owner_dm(message):
        return
    sources = await get_registered_sources(active_only=False)
    if not sources:
        await message.answer("No dynamic bots registered.")
        return
    lines = ["<b>DYNAMIC SOURCES</b>"]
    for item in sources[:80]:
        lines.append(f"• <code>{_escape(item.get('source_key'))}</code> | {_escape(item.get('bot_username'))} | {'ON' if item.get('enabled', True) else 'OFF'}")
    await message.answer("\n".join(lines))

async def _set_enabled(message: Message, enabled: bool) -> None:
    if not _owner_dm(message):
        return
    parts = str(message.text or "").split(maxsplit=1)
    if len(parts) != 2:
        await message.answer("Usage: /enablebot source_key" if enabled else "Usage: /disablebot source_key")
        return
    result = await db.settings.update_one({"key": REGISTRY_KEY, "sources.source_key": parts[1].strip().lower()}, {"$set": {"sources.$.enabled": enabled, "sources.$.updated_at": _now()}, "$inc": {"sources.$.version": 1}})
    if not result.matched_count:
        await message.answer("Source key not found.")
        return
    await refresh_dynamic_source_registry()
    await message.answer("✅ Enabled." if enabled else "✅ Disabled. Existing character records were retained.")

@router.message(Command("enablebot"))
async def enablebot(message: Message) -> None:
    await _set_enabled(message, True)

@router.message(Command("disablebot"))
async def disablebot(message: Message) -> None:
    await _set_enabled(message, False)

@router.message(Command("removebot"))
async def removebot(message: Message) -> None:
    if not _owner_dm(message):
        return
    parts = str(message.text or "").split(maxsplit=1)
    if len(parts) != 2:
        await message.answer("Usage: /removebot source_key")
        return
    key = _source_key(parts[1])
    if not key:
        await message.answer("Invalid source key.")
        return
    # Keep the settings document and existing character records intact. Pull
    # exactly one registration; callers can re-add it later if required.
    result = await db.settings.update_one(
        {"key": REGISTRY_KEY, "sources.source_key": key},
        {"$pull": {"sources": {"source_key": key}}, "$set": {"updated_at": _now()}},
    )
    await refresh_dynamic_source_registry()
    await message.answer(
        "✅ Registration removed. Character records remain untouched."
        if result.modified_count else "Source key not found."
    )


@router.message()
async def source_registration_wizard(message: Message) -> None:
    if not _owner_dm(message) or not message.from_user:
        raise SkipHandler()
    pending = await _pending(message.from_user.id)
    if not pending:
        raise SkipHandler()
    if pending.get("step") == "confirm":
        await message.answer("Preview is waiting. Send /confirm or /cancel.")
        return
    value = str(message.text or "").strip()
    draft = dict(pending.get("draft") or {})
    step = pending.get("step")
    try:
        if step == "name":
            draft["name"] = value[:80]
            nxt = "username"
        elif step == "username":
            username = _username(value)
            if username and not USERNAME_RE.fullmatch(username):
                raise ValueError("Invalid bot username.")
            draft["bot_username"] = username
            if username:
                duplicate = await db.settings.find_one(
                    {"key": REGISTRY_KEY, "sources.bot_username": username},
                    {"_id": 1},
                )
                if duplicate:
                    raise ValueError("This bot username is already registered. Use /listbots.")
            nxt = "source_key"
        elif step == "source_key":
            key = _source_key(value)
            if not key:
                raise ValueError("Use lowercase letters, digits and underscores; 2-48 characters.")
            draft["source_key"] = key
            if draft.get("bot_username"):
                # A bot identity cannot silently be rebound to another source
                # key, including when it already belongs to a built-in source.
                builtin_key = BOT_SOURCE_COLLECTION.get(draft["bot_username"])
                if builtin_key and builtin_key != key:
                    raise ValueError(f"This bot already belongs to built-in key {builtin_key}.")
            exists = await db.settings.find_one({"key": REGISTRY_KEY, "sources.source_key": key}, {"_id": 1})
            existing_record = await characters.find_one({"source_key": key}, {"_id": 1})
            if exists or existing_record or key in VALID_COLLECTIONS:
                draft["source_status"] = "EXISTS"
                draft["source_status_reason"] = "existing registry, source records, or built-in source key"
                await message.answer(f"⚠️ EXISTS — <code>{_escape(key)}</code>. No new key will be created. Send REUSE to reuse it.")
                nxt = "reuse"
            else:
                draft["source_status"] = "NEW"
                draft["source_status_reason"] = "no source key or records found"
                await message.answer(f"🆕 NEW — <code>{_escape(key)}</code>")
                nxt = "output_command"
        elif step == "reuse":
            if value.upper() != "REUSE":
                raise ValueError("Send REUSE to continue with existing source key.")
            draft["reuse_existing"] = True
            nxt = "output_command"
        elif step == "output_command":
            command = _command(value)
            if not command:
                raise ValueError("Output command must look like /name.")
            draft["output_command"] = command
            nxt = "mode"
        elif step == "mode":
            mode = value.lower()
            if mode not in VALID_MODES:
                raise ValueError("Choose inline, forward, both, dm, or manual.")
            draft["mode"] = mode
            nxt = "forward_source" if mode in {"forward", "both"} else ("dm_command" if mode == "dm" else "parser")
        elif step == "forward_source":
            if value == "-":
                forward = ""
            elif re.fullmatch(r"-100[0-9]{5,20}", value):
                forward = value
            else:
                forward = _username(value)
                if not USERNAME_RE.fullmatch(forward):
                    raise ValueError("Enter a valid channel username or -100... chat ID.")
            if not forward and draft["mode"] in {"forward", "both"}:
                raise ValueError("Forward modes require a source channel.")
            draft["forward_source"] = forward
            nxt = "parser"
        elif step == "dm_command":
            if value == "-":
                draft["dm_command"] = ""
                draft["mode"] = "manual"
                nxt = "parser"
            elif "{id}" in value and re.fullmatch(r"/[A-Za-z0-9_ ]*\{id\}[A-Za-z0-9_ ]*", value):
                draft["dm_command"] = value
                nxt = "dm_max_id"
            else:
                raise ValueError("Use a safe ID template such as /check {id}, or - for manual only.")
        elif step == "dm_max_id":
            if not value.isdigit() or not (1 <= int(value) <= 10000000):
                raise ValueError("Set a finite maximum ID from 1 to 10,000,000.")
            draft["max_id"] = int(value)
            nxt = "dm_timeout"
        elif step == "dm_timeout":
            if not value.isdigit() or not (5 <= int(value) <= 120):
                raise ValueError("Response timeout must be 5-120 seconds.")
            draft["response_timeout"] = int(value)
            nxt = "dm_max_misses"
        elif step == "dm_max_misses":
            if not value.isdigit() or not (1 <= int(value) <= 100):
                raise ValueError("Maximum consecutive misses must be 1-100.")
            draft["max_no_response"] = int(value)
            nxt = "parser"
        elif step == "parser":
            parser = value.lower()
            if parser not in VALID_PARSERS:
                raise ValueError("Choose builtin or generic.")
            draft["parser_type"] = parser
            nxt = "name_label" if parser == "generic" else "finish"
        elif step == "name_label":
            if not re.fullmatch(r"[A-Za-z0-9 _-]{1,40}", value):
                raise ValueError("Name label must be simple text such as Name.")
            draft["parser_rules"] = {"name_label": value}
            nxt = "id_label"
        elif step == "id_label":
            if value != "-":
                if not re.fullmatch(r"[A-Za-z0-9 _-]{1,40}", value):
                    raise ValueError("ID label must be simple text or -.")
                draft.setdefault("parser_rules", {})["id_label"] = value
            nxt = "finish"
        else:
            raise ValueError("Unknown wizard step. /cancel and start again.")
        if nxt == "finish":
            username = draft.get("bot_username")
            built_in_key = BOT_SOURCE_COLLECTION.get(username) if username else None
            if built_in_key and built_in_key != draft["source_key"]:
                raise ValueError(f"This bot already uses built-in key {built_in_key}; use that key instead.")
            await _save_pending(message.from_user.id, draft, "confirm")
            await message.answer(_preview(draft))
            return
        await _save_pending(message.from_user.id, draft, nxt)
        await _ask(message, nxt)
    except ValueError as exc:
        await message.answer(f"❌ {_escape(exc)}\nTry again or /cancel.")
