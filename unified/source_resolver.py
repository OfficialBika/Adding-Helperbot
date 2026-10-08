from __future__ import annotations

import re
import unicodedata

from aiogram.types import Message

from unified.config import settings
from helper.registry import match_config

STYLIZED_LATIN_TRANSLATION = str.maketrans({
    "ᴀ": "a", "ʙ": "b", "ᴄ": "c", "ᴅ": "d", "ᴇ": "e", "ꜰ": "f",
    "ɢ": "g", "ʜ": "h", "ɪ": "i", "ᴊ": "j", "ᴋ": "k", "ʟ": "l",
    "ғ": "f", "ꝛ": "r", "ꞃ": "r", "ᴍ": "m", "ɴ": "n", "ᴏ": "o",
    "ᴘ": "p", "ʀ": "r", "ꜱ": "s", "ᴛ": "t", "ᴜ": "u", "ᴠ": "v",
    "ᴡ": "w", "ʏ": "y", "ᴢ": "z",
})

COLLECTION_TO_OUTPUT_COMMAND = {
    "items_character_catcher": "/catch",
    "items_character_catcher_fw": "/catch",
    "items_characters_hallow": "/hallow",
    "items_capture_character": "/capture",
    "items_character_seizer": "/seize",
    "items_husbando_grabber": "/grab",
    "items_grab_your_waifu": "/grab",
    "items_grab_your_husbando": "/grab",
    "items_takers_character": "/take",
    "items_catch_your_husbando": "/guess",
    "items_smash_character": "/smash",
    "items_waifux_grab": "/grab",
    "items_catch_your_waifu": "/guess",
    "items_waifu_grabber": "/grab",
    "items_roronoa_zoro": "/challenge",
    "items_character_picker": "/pick",
    "items_bika_character": "/bika",
    "items_senpai_catcher": "/pick",
    "items_super_zeko": "/ziceko",
    "items_orinx_waifu": "/orin",
    "items_immortal_donghua": "/dao",
    "items_kairo_character": "/kairo",
    "items_grabber_fw": "/grab",
}

COMMAND_TO_COLLECTIONS = {
    "/catch": ["items_character_catcher", "items_character_catcher_fw"],
    "/hallow": ["items_characters_hallow"],
    "/capture": ["items_capture_character"],
    "/seize": ["items_character_seizer"],
    "/loot": ["items_capture_character"],
    "/take": ["items_takers_character"],
    "/smash": ["items_smash_character"],
    "/challenge": ["items_roronoa_zoro"],
    "/bika": ["items_bika_character"],
    "/ziceko": ["items_super_zeko"],
    "/orin": ["items_orinx_waifu"],
    "/dao": ["items_immortal_donghua"],
    "/kairo": ["items_kairo_character"],
    "/pick": ["items_character_picker", "items_senpai_catcher"],
    "/grab": [
        "items_grabber_fw", "items_husbando_grabber", "items_grab_your_waifu",
        "items_grab_your_husbando", "items_waifux_grab", "items_waifu_grabber",
    ],
    "/guess": ["items_catch_your_husbando", "items_catch_your_waifu"],
}

BOT_SOURCE_COLLECTION = {
    "@character_catcher_bot": "items_character_catcher",
    "@character_catcher_logs": "items_character_catcher_fw",
    "@characters_hallow_bot": "items_characters_hallow",
    "@hallowuploads": "items_characters_hallow",
    "@capturecharacterbot": "items_capture_character",
    "@capturedatabase": "items_capture_character",
    "@character_seizer_bot": "items_character_seizer",
    "@seizer_database": "items_character_seizer",
    "@characterlootbot": "items_capture_character",
    "@husbando_grabber_bot": "items_grabber_fw",
    "@grab_your_waifu_bot": "items_grab_your_waifu",
    "@grab_your_husbando_bot": "items_grab_your_husbando",
    "@takers_character_bot": "items_takers_character",
    "@catch_your_husbando_bot": "items_catch_your_husbando",
    "@smash_character_bot": "items_smash_character",
    "@waifuxgrabbot": "items_waifux_grab",
    "@waifuxgrab_database": "items_waifux_grab",
    "@waifuxgrabdb": "items_waifux_grab",
    "@catch_your_waifu_bot": "items_catch_your_waifu",
    "@waifu_grabber_bot": "items_grabber_fw",
    "@roronoa_zoro_robot": "items_roronoa_zoro",
    "@character_picker_bot": "items_character_picker",
    "@bikacharacterbot": "items_bika_character",
    "@senpaicatcherbot": "items_senpai_catcher",
    "@fafafawfawfa": "items_senpai_catcher",
    "@super_zeko_bot": "items_super_zeko",
    "@zicekodata_1": "items_super_zeko",
    "@orinx_catcher_waifu_bot": "items_orinx_waifu",
    "@timunagalaya": "items_orinx_waifu",
    "@immortaldonghuabot": "items_immortal_donghua",
    "@picker_database": "items_character_picker",
    "@kairodatabase": "items_kairo_character",
}

BOT_SOURCE_USER_ID = {
    6157455819: "items_character_catcher", 8688011915: "items_characters_hallow",
    7686672468: "items_capture_character", 7595626187: "items_character_seizer",
    6546492683: "items_grabber_fw", 5934263177: "items_grab_your_waifu",
    6212414747: "items_grab_your_husbando", 7691496587: "items_takers_character",
    6763528462: "items_catch_your_husbando", 8336201607: "items_smash_character",
    8649913814: "items_waifux_grab", 6883098627: "items_catch_your_waifu",
    6195436879: "items_grabber_fw", 8359842815: "items_capture_character",
    5284997893: "items_roronoa_zoro", 8307651649: "items_character_picker",
    8768750156: "items_bika_character", 8532697507: "items_senpai_catcher",
    8534437620: "items_super_zeko", 8685992652: "items_orinx_waifu",
    8928030201: "items_immortal_donghua",
}

BOT_SOURCE_CHAT_ID = {
    -1003923540741: "items_bika_character",
    -1003860021274: "items_super_zeko",
    -1003598338404: "items_orinx_waifu",
    -1004397263975: "items_immortal_donghua",
}

BOT_SOURCE_OUTPUT_COMMAND = {
    "@character_catcher_logs": "/catch",
    "@characterlootbot": "/loot",
    "@super_zeko_bot": "/ziceko",
    "@zicekodata_1": "/ziceko",
    "@orinx_catcher_waifu_bot": "/orin",
    "@timunagalaya": "/orin",
    "@immortaldonghuabot": "/dao",
    "@picker_database": "/pick",
    "@kairodatabase": "/kairo",
    "@husbando_grabber_bot": "/grab",
    "@waifu_grabber_bot": "/grab",
}

BOT_SOURCE_OUTPUT_USER_ID = {
    8359842815: "/loot", 8534437620: "/ziceko",
    8685992652: "/orin", 8928030201: "/dao",
}

TITLE_SOURCE_COLLECTION = {
    "character catcher": "items_character_catcher", "character catcher bot": "items_character_catcher",
    "character catcher logs": "items_character_catcher_fw",
    "characters hallow": "items_characters_hallow", "hallow upload": "items_characters_hallow",
    "hallow uploads": "items_characters_hallow", "capture character": "items_capture_character",
    "capture database": "items_capture_character", "character loot": "items_capture_character",
    "character loot bot": "items_capture_character", "character seizer": "items_character_seizer",
    "seizer database": "items_character_seizer", "husbando grabber": "items_grabber_fw",
    "grabber database": "items_grabber_fw", "waifu grabber": "items_grabber_fw",
    "grab your waifu": "items_grab_your_waifu", "grab your husbando": "items_grab_your_husbando",
    "waifuxgrab": "items_waifux_grab", "waifuxgrab database": "items_waifux_grab",
    "grab garden": "items_waifux_grab", "takers character": "items_takers_character",
    "catch your husbando": "items_catch_your_husbando", "catch your waifu": "items_catch_your_waifu",
    "smash character": "items_smash_character", "roronoa zoro": "items_roronoa_zoro",
    "character picker": "items_character_picker", "picker database": "items_character_picker",
    "bika waifu database": "items_bika_character", "bika character bot": "items_bika_character",
    "senpai catcher": "items_senpai_catcher", "senpaicatcher": "items_senpai_catcher",
    "senpai database": "items_senpai_catcher", "myanmar character": "items_super_zeko",
    "myanmar character logs": "items_super_zeko", "super zeko": "items_super_zeko",
    "ziceko data": "items_super_zeko", "orinx waifu": "items_orinx_waifu",
    "orinx waifu bot": "items_orinx_waifu", "timunagalaya": "items_orinx_waifu",
    "immortal donghua": "items_immortal_donghua", "donghua database": "items_immortal_donghua",
    "kairo database": "items_kairo_character", "kairo collect": "items_kairo_character",
}

TITLE_OUTPUT_COMMAND = {
    "character loot": "/loot", "character loot bot": "/loot",
    "roronoa zoro": "/challenge", "character picker": "/pick", "picker database": "/pick",
    "bika waifu database": "/bika", "bika character bot": "/bika",
    "senpai catcher": "/pick", "senpaicatcher": "/pick", "senpai database": "/pick",
    "myanmar character": "/ziceko", "super zeko": "/ziceko", "ziceko data": "/ziceko",
    "orinx waifu": "/orin", "orinx waifu bot": "/orin", "timunagalaya": "/orin",
    "immortal donghua": "/dao", "donghua database": "/dao",
    "kairo database": "/kairo", "kairo collect": "/kairo",
}

CONTENT_SOURCE_RULES = [
    (re.compile(r"media\s*\+\s*🎴.*?\|\s*.*?(?:🎬\s*anime|🆔\s*id\s*:)", re.I | re.S), "items_senpai_catcher", "/pick"),
    (re.compile(r"⚖️\s*character\s+valuation.*?🎴\s*name\s*:", re.I | re.S), "items_senpai_catcher", "/pick"),
    (re.compile(r"🚫\s*character\s+with\s+id\s+\d+\s+not\s+found", re.I), "items_senpai_catcher", "/pick"),
    (re.compile(r"owo!\s*check\s+out\s+this\s+(?:husbando|waifu)", re.I | re.S), "items_grabber_fw", "/grab"),
    (re.compile(r"global\s+character\s+info.*(?:series|id)\s*:", re.I | re.S), "items_waifux_grab", "/grab"),
    (re.compile(r"media\s*\+\s*owo!\s*check\s+out\s+this\s+waifu", re.I | re.S), "items_grab_your_waifu", "/grab"),
    (re.compile(r"media\s*\+\s*.*?name\s*:.*rarity\s*:.*anime\s*:.*id\s*:", re.I | re.S), "items_grab_your_waifu", "/grab"),
    (re.compile(r"new\s+waifu\s+added|item\s*id\s*[:：].*\bname\b\s*[:：].*\brarity\b", re.I | re.S), "items_waifux_grab", "/grab"),
    (re.compile(r"new\s+character\s+added\s+to\s+the\s+bot|char\s*id\s*[:：].*\bname\b\s*[:：].*\banime\b", re.I | re.S), "items_senpai_catcher", "/pick"),
    (re.compile(r"character\s+database.*\bid\b\s*[:：].*\bname\b\s*[:：].*\bseries\b", re.I | re.S), "items_orinx_waifu", "/orin"),
    (re.compile(r"card\s+drop|myanmar\s+character|/ziceko|တင်ပြီးပြီ|uploaded\s*\(/?li\)|📛.*name|⭐.*rarity", re.I | re.S), "items_super_zeko", "/ziceko"),
    (re.compile(r"(?:saved|updated).*\bname\b\s*[:：].*\bid\b\s*[:：].*\brarity\b\s*[:：].*\banime\b", re.I | re.S), "items_immortal_donghua", "/dao"),
]

USING_RE = re.compile(r"(?:using|use|hint|full|cmd|command)\s*[:：\-=]?\s*(/[a-zA-Z0-9_]+)(?:@[A-Za-z0-9_]+)?", re.I)
CMD_RE = re.compile(r"(^|\s)(/[a-zA-Z0-9_]+)(?:@[A-Za-z0-9_]+)?(?=\s|$|[^A-Za-z0-9_@])", re.I)


def _norm_text(value: str | None) -> str:
    raw = value or ""
    return unicodedata.normalize("NFKC", raw.translate(STYLIZED_LATIN_TRANSLATION)).translate(STYLIZED_LATIN_TRANSLATION)


def _clean_title(value: str | None) -> str:
    value = _norm_text(value).lower().strip().replace("_", " ")
    value = re.sub(r"[^0-9a-z\u1000-\u109f\s]+", " ", value)
    return re.sub(r"\s+", " ", value).strip()


def _message_text(message: Message) -> str:
    parts: list[str] = []
    for obj in (message, getattr(message, "external_reply", None)):
        if obj is None:
            continue
        for attr in ("caption", "text", "html_text", "md_text"):
            value = getattr(obj, attr, None)
            if isinstance(value, str) and value.strip():
                parts.append(_norm_text(value))
    return "\n".join(parts)


def source_origin_chat(message: Message | None):
    if message is None:
        return None
    origin = getattr(message, "forward_origin", None)
    if origin is not None:
        return getattr(origin, "chat", None) or getattr(origin, "sender_chat", None)
    return getattr(message, "forward_from_chat", None) or getattr(message, "sender_chat", None)


def source_chat_id(message: Message) -> int | None:
    chat = source_origin_chat(message)
    try:
        return int(chat.id) if chat is not None and getattr(chat, "id", None) is not None else None
    except Exception:
        return None


def source_origin_message_id(message: Message) -> int | None:
    origin = getattr(message, "forward_origin", None)
    raw = getattr(origin, "message_id", None) if origin else None
    if raw is None:
        raw = getattr(message, "forward_from_message_id", None)
    try:
        return int(raw) if raw is not None else None
    except Exception:
        return None


def source_origin_key(message: Message) -> tuple[int, int] | None:
    chat_id, message_id = source_chat_id(message), source_origin_message_id(message)
    return (chat_id, message_id) if chat_id is not None and message_id is not None else None


def _normalize_username(value: str | None) -> str | None:
    value = (value or "").strip().lower().lstrip("@")
    return f"@{value}" if value else None


def source_user_id(message: Message) -> int | None:
    origin = getattr(message, "forward_origin", None)
    sender_user = getattr(origin, "sender_user", None) if origin else None
    for user in (
        sender_user, getattr(message, "via_bot", None), getattr(message, "forward_from", None),
        getattr(message, "from_user", None) if getattr(getattr(message, "from_user", None), "is_bot", False) else None,
    ):
        value = getattr(user, "id", None) if user is not None else None
        if value is not None:
            try:
                return int(value)
            except Exception:
                pass
    return None


def source_username(message: Message) -> str | None:
    chat = source_origin_chat(message)
    if chat is not None and getattr(chat, "username", None):
        return _normalize_username(chat.username)
    origin = getattr(message, "forward_origin", None)
    sender_user = getattr(origin, "sender_user", None) if origin else None
    for user in (
        sender_user, getattr(message, "via_bot", None),
        getattr(message, "forward_from", None), getattr(message, "from_user", None)
    ):
        if user is not None and getattr(user, "username", None):
            return _normalize_username(user.username)
    return None


def source_title(message: Message) -> str | None:
    chat = source_origin_chat(message)
    if chat is not None and getattr(chat, "title", None):
        return str(chat.title)
    origin = getattr(message, "forward_origin", None)
    sender_user = getattr(origin, "sender_user", None) if origin else None
    if sender_user is not None:
        value = getattr(sender_user, "full_name", None) or ""
        if value:
            return str(value)
    hidden = getattr(origin, "sender_user_name", None) if origin else None
    return str(hidden).strip() if hidden else None


def _title_match(mapping: dict[str, str], title: str | None) -> str | None:
    cleaned = _clean_title(title)
    if not cleaned:
        return None
    if cleaned in mapping:
        return mapping[cleaned]
    for key, value in mapping.items():
        if key in cleaned or cleaned in key:
            return value
    return None


def command_from_text(text: str | None) -> str | None:
    if not text:
        return None
    value = _norm_text(text).strip()
    first = value.split(maxsplit=1)[0].lower().split("@", 1)[0] if value else ""
    if first in COMMAND_TO_COLLECTIONS:
        return first
    match = USING_RE.search(value) or CMD_RE.search(value)
    if not match:
        return None
    cmd = match.group(match.lastindex or 1).lower().split("@", 1)[0]
    return cmd if cmd in COMMAND_TO_COLLECTIONS else None


def grabber_source_variant(message: Message) -> str | None:
    username = source_username(message)
    if username == "@husbando_grabber_bot":
        return "husbando_grabber"
    if username == "@waifu_grabber_bot":
        return "waifu_grabber"

    user_id = source_user_id(message)
    if user_id == 6546492683:
        return "husbando_grabber"
    if user_id == 6195436879:
        return "waifu_grabber"

    text = _message_text(message)
    if re.search(r"owo!\s*check\s+out\s+this\s+husbando", text, re.I):
        return "husbando_grabber"
    if re.search(r"owo!\s*check\s+out\s+this\s+waifu", text, re.I):
        return "waifu_grabber"

    signature = next(
        (
            getattr(obj, "author_signature", None)
            for obj in (getattr(message, "forward_origin", None), message)
            if getattr(obj, "author_signature", None)
        ),
        None,
    )
    normalized = _clean_title(str(signature)) if signature else ""
    if "waifu grabber bot" in normalized:
        return "waifu_grabber"
    if "husbando grabber bot" in normalized:
        return "husbando_grabber"
    return None


def _content_source(message: Message):
    text = _message_text(message)
    for pattern, collection, command in CONTENT_SOURCE_RULES:
        if pattern.search(text):
            return collection, command
    return None, None


def resolve_trusted_inline_collection(message: Message) -> str | None:
    text = _message_text(message)
    if re.search(r"owo!\s*check\s+out\s+this\s+waifu", text, re.I):
        return "items_grab_your_waifu"
    if re.search(r"owo!\s*check\s+out\s+this\s+character", text, re.I):
        return "items_character_catcher"
    if re.search(r"media\s*\+\s*🎴.*?(?:🎬\s*anime|🆔\s*id\s*:)", text, re.I | re.S):
        return "items_senpai_catcher"
    if re.search(r"⚖️\s*character\s+valuation.*?🎴\s*name\s*:", text, re.I | re.S):
        return "items_senpai_catcher"
    return None


def resolve_source_collection(message: Message) -> str | None:
    username = source_username(message)
    dynamic = match_config(
        username=username,
        user_id=source_user_id(message),
        chat_id=source_chat_id(message),
        title=source_title(message),
        forward=bool(getattr(message, "forward_origin", None) or getattr(message, "forward_from_chat", None)),
    )
    if dynamic:
        return dynamic.key
    if username and username in BOT_SOURCE_COLLECTION:
        return BOT_SOURCE_COLLECTION[username]

    user_id = source_user_id(message)
    if user_id is not None and user_id in BOT_SOURCE_USER_ID:
        return BOT_SOURCE_USER_ID[user_id]

    chat_id = source_chat_id(message)
    if chat_id is not None and chat_id in BOT_SOURCE_CHAT_ID:
        return BOT_SOURCE_CHAT_ID[chat_id]

    value = _title_match(TITLE_SOURCE_COLLECTION, source_title(message))
    if value:
        return value

    value, _ = _content_source(message)
    if value:
        return value

    title = source_title(message) or ""
    text = f"{title}\n{_message_text(message)}".lower()
    command = settings.forward_source_commands.get(username or "")
    if command is None:
        for key, configured in settings.forward_source_commands.items():
            if key and key.lower() in text:
                command = configured
                break
    if command:
        cols = COMMAND_TO_COLLECTIONS.get(command, [])
        if cols:
            return cols[0]

    command = command_from_text(_message_text(message))
    cols = COMMAND_TO_COLLECTIONS.get(command or "", [])
    return cols[0] if len(cols) == 1 else None


def output_command_from_message(message: Message, collection: str | None = None) -> str | None:
    dynamic = match_config(
        username=source_username(message),
        user_id=source_user_id(message),
        chat_id=source_chat_id(message),
        title=source_title(message),
        forward=bool(getattr(message, "forward_origin", None) or getattr(message, "forward_from_chat", None)),
    )
    if dynamic:
        return dynamic.command

    username = source_username(message)
    if username and username in BOT_SOURCE_OUTPUT_COMMAND:
        return BOT_SOURCE_OUTPUT_COMMAND[username]

    user_id = source_user_id(message)
    if user_id is not None and user_id in BOT_SOURCE_OUTPUT_USER_ID:
        return BOT_SOURCE_OUTPUT_USER_ID[user_id]

    value = _title_match(TITLE_OUTPUT_COMMAND, source_title(message))
    if value:
        return value

    _, value = _content_source(message)
    if value:
        return value

    command = command_from_text(_message_text(message))
    if command and (not collection or collection in COMMAND_TO_COLLECTIONS.get(command, [])):
        return command

    return COLLECTION_TO_OUTPUT_COMMAND.get(collection) if collection else None
