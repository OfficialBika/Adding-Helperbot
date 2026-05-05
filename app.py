import asyncio
import hashlib
import logging
import os
import re
import shlex
import tempfile
import unicodedata
from dataclasses import dataclass
from datetime import datetime, timezone
from io import BytesIO
from typing import Any, Optional

import cv2
import imagehash
from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandObject
from aiogram.types import BotCommand, Message
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application
from dotenv import load_dotenv
from motor.motor_asyncio import AsyncIOMotorClient
from PIL import Image

load_dotenv()

# -----------------------------------------------------
# Config
# -----------------------------------------------------
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
MONGO_URI = os.getenv("MONGO_URI", "").strip()
DB_NAME = os.getenv("DB_NAME", "waifu_adding_v2").strip()

OWNER_IDS = {
    int(x.strip())
    for x in os.getenv("OWNER_IDS", os.getenv("OWNER_ID", "")).split(",")
    if x.strip().isdigit()
}

PHOTO_PHASH_THRESHOLD = int(os.getenv("PHOTO_PHASH_THRESHOLD", "8"))
VIDEO_FRAME_THRESHOLD = int(os.getenv("VIDEO_FRAME_THRESHOLD", "10"))
VIDEO_AVG_THRESHOLD = int(os.getenv("VIDEO_AVG_THRESHOLD", "12"))
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()
OWNER_USERNAME = os.getenv("OWNER_USERNAME", "@Official_Bika").strip()
DEFAULT_COMMAND = os.getenv("DEFAULT_COMMAND", "/hallow").strip() or "/hallow"
DEFAULT_SOURCE_KEY = os.getenv("DEFAULT_SOURCE_KEY", "characters_hallow").strip() or "characters_hallow"
ADDED_LOG_CHANNEL = os.getenv("ADDED_LOG_CHANNEL", "@WaifuAddedList").strip()

DEFAULT_TARGET_CHAT_RAW = os.getenv("DEFAULT_TARGET_CHAT", "").strip()
DEFAULT_TARGET_CHAT = (
    int(DEFAULT_TARGET_CHAT_RAW)
    if DEFAULT_TARGET_CHAT_RAW and DEFAULT_TARGET_CHAT_RAW.lstrip("-").isdigit()
    else None
)

USE_WEBHOOK = os.getenv("USE_WEBHOOK", "false").lower() == "true"
PUBLIC_URL = os.getenv("PUBLIC_URL", "").strip()
WEBHOOK_PATH = os.getenv("WEBHOOK_PATH", "/webhook").strip() or "/webhook"
WEBHOOK_SECRET = os.getenv("WEBHOOK_SECRET", "").strip()
PORT = int(os.getenv("PORT", "8080"))

# Telegram /restart command -> PM2 restart (owner only)
ENABLE_TELEGRAM_RESTART = os.getenv("ENABLE_TELEGRAM_RESTART", "false").lower() == "true"
PM2_PROCESS_NAME = os.getenv("PM2_PROCESS_NAME", "adderbotv2").strip() or "adderbotv2"
PM2_BIN = os.getenv("PM2_BIN", "pm2").strip() or "pm2"

if not BOT_TOKEN:
    raise RuntimeError("BOT_TOKEN is required")
if not MONGO_URI:
    raise RuntimeError("MONGO_URI is required")
if not OWNER_IDS:
    raise RuntimeError("OWNER_ID or OWNER_IDS is required")
if USE_WEBHOOK and (not PUBLIC_URL or not WEBHOOK_SECRET):
    raise RuntimeError("PUBLIC_URL and WEBHOOK_SECRET are required when USE_WEBHOOK=true")

logging.basicConfig(
    level=getattr(logging, LOG_LEVEL, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
logger = logging.getLogger("adding-bot")

# -----------------------------------------------------
# Database
# -----------------------------------------------------
client = AsyncIOMotorClient(MONGO_URI)
db = client[DB_NAME]
# old collection name is kept only for compatibility, new saves use source collections
items = db.items
sudo_users = db.sudo_users
known_users = db.known_users
user_modes = db.user_modes
settings_col = db.settings

router = Router()

# -----------------------------------------------------
# Data models
# -----------------------------------------------------
@dataclass(frozen=True)
class SourceDef:
    key: str
    collection: str
    command: str
    bot_username: str
    inline_usernames: tuple[str, ...] = ()
    forward_usernames: tuple[str, ...] = ()
    forward_titles: tuple[str, ...] = ()
    parser: str = "auto"
    save_rarity: bool = True


@dataclass
class MediaMeta:
    media_type: str
    file_id: str
    file_unique_id: str
    sha256: str
    phash: Optional[str] = None
    frame_hashes: Optional[list[str]] = None


@dataclass
class ParsedText:
    name: Optional[str]
    anime_name: Optional[str]
    rarity: Optional[str]
    card_id: Optional[str]
    command_name: Optional[str]
    raw_text: str
    source_key: Optional[str] = None


@dataclass
class SourceUpdate:
    source_key: str
    update_type: str
    old_name: Optional[str] = None
    new_name: Optional[str] = None
    new_rarity: Optional[str] = None
    raw_text: str = ""


# -----------------------------------------------------
# Helpers: text clean / regex
# -----------------------------------------------------
def html_escape(text: str) -> str:
    return (text or "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def clean_value(value: str) -> str:
    return re.sub(r"\s+", " ", value or "").strip()


def normalize_name(name: str) -> str:
    return clean_value(name).casefold()


def normalize_parse_text(text: Optional[str]) -> str:
    text = text or ""
    text = unicodedata.normalize("NFKC", text)
    text = text.replace("\r", "\n")
    text = text.replace("：", ":").replace("﹕", ":").replace("꞉", ":")
    text = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", text)
    text = re.sub(r"[ \t]+", " ", text)
    return text.strip()


def strip_leading_symbols(value: str) -> str:
    value = clean_value(value)
    # Keep normal letters/numbers and CJK/Japanese/Korean. Remove leading emoji/bullets only.
    return re.sub(r"^[^\w\u00C0-\u024F\u0400-\u04FF\u3040-\u30FF\u4E00-\u9FFF\uAC00-\uD7AF]+", "", value).strip()


def strip_grab_name_suffix(value: str) -> str:
    value = clean_value(value)
    return clean_value(re.sub(r"\s*[-–—|]+\s*(?:rarity|anime|id)\b.*$", "", value, flags=re.IGNORECASE))


def clean_rarity_value(value: str) -> str:
    value = clean_value(value)
    value = value.strip("()[]{} ")
    # Remove leading emoji/symbols, keep first text part.
    value = strip_leading_symbols(value)
    # Remove leftover closing brackets at end.
    value = value.strip("()[]{} ")
    return clean_value(value)


def clean_command_name(value: str) -> str:
    cmd = clean_value(value)
    if not cmd:
        return DEFAULT_COMMAND
    if not cmd.startswith("/"):
        cmd = f"/{cmd.lstrip('/')}"
    return cmd.split()[0].lower()


def normalize_forward_mapping_key(value: str) -> str:
    return clean_value(value).lstrip("@").casefold()


def norm_username(value: str) -> str:
    return clean_value(value).lstrip("@").lower()


NAME_PATTERNS = [
    re.compile(r"^[^\n\r]*?Character\s*Name\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE),
    re.compile(r"^[^\n\r]*?\bName\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE),
]

ANIME_PATTERNS = [
    re.compile(r"^[^\n\r]*?Anime\s*Name\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE),
    re.compile(r"^[^\n\r]*?\bAnime\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE),
    re.compile(r"^[^\n\r]*?\bSeries\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE),
]

RARITY_PATTERNS = [
    re.compile(r"^[^\n\r]*?\bRarity\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE),
    re.compile(r"\bRARITY\b\s*[:\-]?\s*[\(\[]?\s*(.+?)\s*[\)\]]?\s*$", re.IGNORECASE | re.MULTILINE),
]

CARD_ID_PATTERNS = [
    re.compile(r"^[^\n\r]*?\bCharacter\s*ID\b\s*[:\-]?\s*#?\s*([0-9]+)\s*$", re.IGNORECASE | re.MULTILINE),
    re.compile(r"^[^\n\r]*?\bCard\s*ID\b\s*[:\-]?\s*#?\s*([0-9]+)\s*$", re.IGNORECASE | re.MULTILINE),
    re.compile(r"^[^\n\r]*?\bID\b\s*(?:ID)?\s*[:\-]?\s*#?\s*([0-9]+)\s*$", re.IGNORECASE | re.MULTILINE),
    re.compile(r"^[^\n\r]*?🆔\s*[:\-]?\s*#?\s*([0-9]+)\s*$", re.IGNORECASE | re.MULTILINE),
]

COMMAND_PATTERNS = [
    re.compile(r"(?:using|use|hint|full).*?/\s*([A-Za-z0-9_]+)\b", re.IGNORECASE | re.DOTALL),
    re.compile(r"/\s*([A-Za-z0-9_]+)\s*(?:\[[^\]]*name[^\]]*\]|\([^\)]*name[^\)]*\)|\bname\b)", re.IGNORECASE | re.DOTALL),
    re.compile(r"/\s*([A-Za-z0-9_]+)\b", re.IGNORECASE),
]

OWO_HEADER_RE = re.compile(
    r"OwO!\s*Check\s+out\s+(?:this\s+)?(?:character|husbando|waifu)!!?",
    re.IGNORECASE,
)
ID_NAME_COLON_RE = re.compile(r"^\s*(?:ID\s*)?(\d+)\s*[:\-]\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
ID_NAME_SPACE_RE = re.compile(r"^\s*(\d+)\s+(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
ID_NAME_LINE_RE = re.compile(r"^\s*(?:🆔|ID|Id|id)?\s*#?\s*(\d+)\s*[:：]\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)

SMASH_ID_RE = re.compile(r"^[^\n\r]*?(?:\bID\b|🆔)\s*[:\-]?\s*#?\s*([0-9]+)\s*$", re.IGNORECASE | re.MULTILINE)
WAIFUX_NAME_RE = re.compile(r"^[^\n\r]*?➤\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
WAIFUX_SERIES_RE = re.compile(r"^[^\n\r]*?\bSeries\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
WAIFUX_ID_RE = re.compile(r"^[^\n\r]*?\bID\b\s*[:\-]?\s*#?\s*([0-9]+)\s*$", re.IGNORECASE | re.MULTILINE)

RARITY_UPDATE_NAME_RE = re.compile(r"^[^\n\r]*?\bWaifu\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
RARITY_UPDATE_NEW_RE = re.compile(r"^[^\n\r]*?\bNew\s+Rarity\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
RENAME_OLD_NAME_RE = re.compile(r"^[^\n\r]*?\bOld\s+Name\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
RENAME_NEW_NAME_RE = re.compile(r"^[^\n\r]*?\bNew\s+Name\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)


def parse_field(text: str, patterns: list[re.Pattern]) -> Optional[str]:
    for pattern in patterns:
        match = pattern.search(text or "")
        if match:
            return clean_value(match.group(1))
    return None


def parse_command_name(text: str) -> Optional[str]:
    raw = unicodedata.normalize("NFKC", normalize_parse_text(text or ""))
    for pattern in COMMAND_PATTERNS:
        match = pattern.search(raw)
        if match:
            return clean_command_name("/" + match.group(1))
    return None


def finalize_parsed_text(parsed: ParsedText) -> ParsedText:
    parsed.name = strip_grab_name_suffix(strip_leading_symbols(parsed.name or "")) or None
    parsed.anime_name = strip_leading_symbols(parsed.anime_name or "") or None
    parsed.rarity = clean_rarity_value(parsed.rarity or "") or None
    parsed.card_id = clean_value(parsed.card_id or "") or None
    if parsed.command_name:
        parsed.command_name = clean_command_name(parsed.command_name)
    parsed.raw_text = normalize_parse_text(parsed.raw_text)
    return parsed


# -----------------------------------------------------
# Source registry: source တစ်ခု = collection တစ်ခု
# -----------------------------------------------------
SOURCE_CONFIGS: list[SourceDef] = [
    SourceDef("character_catcher", "items_character_catcher", "/catch", "@Character_Catcher_Bot", ("Character_Catcher_Bot",), parser="owo_colon"),
    SourceDef("characters_hallow", "items_characters_hallow", "/hallow", "@Characters_Hallow_bot", ("Characters_Hallow_bot",), ("hallowuploads",), ("Hallow Upload",), parser="label"),
    SourceDef("capture_character", "items_capture_character", "/capture", "@CaptureCharacterBot", ("CaptureCharacterBot", "capturecharacterbot", "capture_character_bot"), ("CaptureDatabase",), ("CAPTURE|UPLOADS", "Capture Uploads", "Capture Database"), parser="capture"),
    SourceDef("character_seizer", "items_character_seizer", "/seize", "@character_seizer_bot", ("character_seizer_bot", "Character_Seizer_Bot"), ("Seizer_Database",), ("SEIZER DATABASE", "Seizer Database"), parser="seizer"),
    SourceDef("husbando_grabber", "items_husbando_grabber", "/grab", "@Husbando_Grabber_Bot", ("Husbando_Grabber_Bot", "husbando_grabber_bot"), parser="owo_colon"),
    SourceDef("grab_your_waifu", "items_grab_your_waifu", "/grab", "@Grab_Your_Waifu_Bot", ("Grab_Your_Waifu_Bot", "grab_your_waifu_bot"), parser="label"),
    SourceDef("grab_your_husbando", "items_grab_your_husbando", "/grab", "@Grab_Your_Husbando_Bot", ("Grab_Your_Husbando_Bot", "grab_your_husbando_bot"), parser="label"),
    SourceDef("takers_character", "items_takers_character", "/take", "@Takers_character_bot", ("Takers_character_bot", "takers_character_bot"), parser="owo_space"),
    SourceDef("catch_your_husbando", "items_catch_your_husbando", "/guess", "@Catch_Your_Husbando_Bot", ("Catch_Your_Husbando_Bot", "catch_your_husbando_bot"), parser="owo_colon"),
    SourceDef("smash_character", "items_smash_character", "/smash", "@Smash_Character_Bot", ("Smash_Character_Bot", "smash_character_bot"), parser="smash"),
    SourceDef("waifux_grab", "items_waifux_grab", "/grab", "@WaifuxGrabBot", ("WaifuxGrabBot", "waifuxgrabbot"), parser="waifux", save_rarity=False),
    SourceDef("catch_your_waifu", "items_catch_your_waifu", "/guess", "@Catch_Your_Waifu_Bot", ("Catch_Your_Waifu_Bot", "catch_your_waifu_bot"), parser="owo_colon"),
    SourceDef("waifu_grabber", "items_waifu_grabber", "/grab", "@Waifu_Grabber_Bot", ("Waifu_Grabber_Bot", "waifu_grabber_bot"), parser="owo_colon"),
]

SOURCE_BY_KEY = {src.key: src for src in SOURCE_CONFIGS}
SOURCE_BY_INLINE_USERNAME: dict[str, SourceDef] = {}
SOURCE_BY_FORWARD_USERNAME: dict[str, SourceDef] = {}
SOURCE_BY_FORWARD_TITLE: dict[str, SourceDef] = {}

for src in SOURCE_CONFIGS:
    for username in (src.bot_username, *src.inline_usernames):
        key = norm_username(username)
        if key:
            SOURCE_BY_INLINE_USERNAME[key] = src
    for username in src.forward_usernames:
        key = norm_username(username)
        if key:
            SOURCE_BY_FORWARD_USERNAME[key] = src
    for title in src.forward_titles:
        key = normalize_forward_mapping_key(title)
        if key:
            SOURCE_BY_FORWARD_TITLE[key] = src


def get_source_collection(source_key: Optional[str]):
    src = SOURCE_BY_KEY.get(source_key or "")
    if src:
        return db[src.collection]
    return db["items_unknown"]


def get_default_source_key_from_command(command_name: str) -> str:
    cmd = clean_command_name(command_name)
    for src in SOURCE_CONFIGS:
        if src.command == cmd:
            return src.key
    return DEFAULT_SOURCE_KEY


def get_source_bot_key_from_command(command_name: str) -> str:
    return get_default_source_key_from_command(command_name)


# -----------------------------------------------------
# Telegram source helpers
# -----------------------------------------------------
def collect_candidate_texts(message: Message) -> list[str]:
    candidates: list[str] = []
    for value in [getattr(message, "caption", None), getattr(message, "text", None)]:
        value = normalize_parse_text(value)
        if value and value not in candidates:
            candidates.append(value)
    ext = getattr(message, "external_reply", None)
    if ext is not None:
        for value in [getattr(ext, "caption", None), getattr(ext, "text", None)]:
            value = normalize_parse_text(value)
            if value and value not in candidates:
                candidates.append(value)
    return candidates


def get_combined_message_text(message: Message) -> str:
    return "\n".join(collect_candidate_texts(message)).strip()


def extract_media_handle(message: Message):
    if message.photo:
        return "photo", message.photo[-1]
    if message.video:
        return "video", message.video
    if getattr(message, "animation", None):
        return "video", message.animation
    document = getattr(message, "document", None)
    if document and str(getattr(document, "mime_type", "") or "").startswith("video/"):
        return "video", document
    return None, None


def is_group_chat(message: Message) -> bool:
    return bool(message.chat and getattr(message.chat, "type", "") in {"group", "supergroup"})


def is_private_chat(message: Message) -> bool:
    return bool(message.chat and getattr(message.chat, "type", "") == "private")


def is_default_target_chat(message: Message) -> bool:
    return bool(DEFAULT_TARGET_CHAT is not None and message.chat and message.chat.id == DEFAULT_TARGET_CHAT)


def get_inline_source_username(message: Message) -> str:
    via_bot = getattr(message, "via_bot", None)
    if via_bot is None:
        return ""
    return norm_username(getattr(via_bot, "username", "") or "")


def get_inline_source_def(message: Message) -> Optional[SourceDef]:
    return SOURCE_BY_INLINE_USERNAME.get(get_inline_source_username(message))


def get_inline_source_command(message: Message) -> Optional[str]:
    src = get_inline_source_def(message)
    return src.command if src else None


def is_forwarded_message(message: Message) -> bool:
    return bool(
        getattr(message, "forward_origin", None)
        or getattr(message, "forward_from_chat", None)
        or getattr(message, "forward_from", None)
        or getattr(message, "forward_sender_name", None)
    )


def get_forward_source_info(message: Message) -> dict[str, Any]:
    info: dict[str, Any] = {"chat_id": None, "username": "", "title": "", "origin_type": ""}
    origin = getattr(message, "forward_origin", None)
    if origin:
        info["origin_type"] = origin.__class__.__name__
        chat = getattr(origin, "chat", None) or getattr(origin, "sender_chat", None)
        if chat is not None:
            info["chat_id"] = getattr(chat, "id", None)
            info["username"] = norm_username(getattr(chat, "username", "") or "")
            info["title"] = normalize_forward_mapping_key(getattr(chat, "title", "") or "")
            return info
        sender_user_name = norm_username(getattr(origin, "sender_user_name", "") or "")
        if sender_user_name:
            info["username"] = sender_user_name
            return info
    legacy_chat = getattr(message, "forward_from_chat", None)
    if legacy_chat is not None:
        info["chat_id"] = getattr(legacy_chat, "id", None)
        info["username"] = norm_username(getattr(legacy_chat, "username", "") or "")
        info["title"] = normalize_forward_mapping_key(getattr(legacy_chat, "title", "") or "")
        info["origin_type"] = "legacy_forward_chat"
        return info
    sender_chat = getattr(message, "sender_chat", None)
    if sender_chat is not None:
        info["chat_id"] = getattr(sender_chat, "id", None)
        info["username"] = norm_username(getattr(sender_chat, "username", "") or "")
        info["title"] = normalize_forward_mapping_key(getattr(sender_chat, "title", "") or "")
        info["origin_type"] = "sender_chat"
        return info
    return info


def get_forward_source_def(message: Message) -> Optional[SourceDef]:
    if not is_forwarded_message(message):
        return None
    info = get_forward_source_info(message)
    username = normalize_forward_mapping_key(info.get("username", ""))
    title = normalize_forward_mapping_key(info.get("title", ""))
    if username and username in SOURCE_BY_FORWARD_USERNAME:
        return SOURCE_BY_FORWARD_USERNAME[username]
    if title and title in SOURCE_BY_FORWARD_TITLE:
        return SOURCE_BY_FORWARD_TITLE[title]
    for key, src in SOURCE_BY_FORWARD_TITLE.items():
        if key and title and (key in title or title in key):
            return src
    return None


def get_forward_source_command(message: Message) -> Optional[str]:
    src = get_forward_source_def(message)
    return src.command if src else None


def is_allowed_forward_source(message: Message) -> bool:
    return is_forwarded_message(message) and bool(get_forward_source_def(message))


def get_autosave_source_label(message: Message) -> str:
    inline_username = get_inline_source_username(message)
    if inline_username:
        return f"inline @{inline_username}"
    source_info = get_forward_source_info(message)
    return source_info.get("title") or source_info.get("username") or str(source_info.get("chat_id") or "forwarded source")


def get_log_source_label(message: Message) -> str:
    if get_inline_source_command(message):
        return get_autosave_source_label(message)
    if is_allowed_forward_source(message):
        return get_autosave_source_label(message)
    if is_forwarded_message(message):
        return get_autosave_source_label(message)
    return "manual-save"


# -----------------------------------------------------
# Parsers
# -----------------------------------------------------
def lines_from_text(raw: str) -> list[str]:
    return [clean_value(x) for x in normalize_parse_text(raw).splitlines() if clean_value(x)]


def parse_label_message(message: Message, src: SourceDef) -> ParsedText:
    raw = get_combined_message_text(message)
    parsed = ParsedText(
        name=parse_field(raw, NAME_PATTERNS),
        anime_name=parse_field(raw, ANIME_PATTERNS),
        rarity=parse_field(raw, RARITY_PATTERNS) if src.save_rarity else None,
        card_id=parse_field(raw, CARD_ID_PATTERNS),
        command_name=src.command,
        raw_text=raw,
        source_key=src.key,
    )
    return finalize_parsed_text(parsed)


def infer_anime_from_lines(lines: list[str], match_line_index: int) -> Optional[str]:
    if match_line_index <= 0:
        return None
    for i in range(match_line_index - 1, -1, -1):
        line = clean_value(lines[i])
        if not line:
            continue
        if OWO_HEADER_RE.search(line):
            continue
        if re.search(r"\b(?:rarity|added\s*by|price|global\s+owners|globally\s+catches|event|status|id|character\s*id)\b", line, re.IGNORECASE):
            continue
        if re.search(r"new\s+(?:character|waifu|husbando)\s+added", line, re.IGNORECASE):
            continue
        return strip_leading_symbols(line) or None
    return None


def parse_owo_message(message: Message, src: SourceDef, mode: str = "colon") -> ParsedText:
    raw = get_combined_message_text(message)
    lines = lines_from_text(raw)
    regexes = [ID_NAME_LINE_RE]
    if mode == "space":
        regexes = [ID_NAME_SPACE_RE, ID_NAME_LINE_RE, ID_NAME_COLON_RE]
    else:
        regexes = [ID_NAME_LINE_RE, ID_NAME_COLON_RE, ID_NAME_SPACE_RE]

    name = None
    card_id = None
    anime_name = None
    match_line = ""
    for regex in regexes:
        match = regex.search(raw)
        if match:
            # Avoid taking pure ID label lines like ID: 100 without name.
            if len(match.groups()) >= 2:
                card_id = clean_value(match.group(1))
                name = clean_value(match.group(2))
                match_line = clean_value(match.group(0))
                break
    if match_line in lines:
        anime_name = infer_anime_from_lines(lines, lines.index(match_line))
    else:
        # fallback: first non-header line before id/name
        for line in lines:
            if OWO_HEADER_RE.search(line):
                continue
            if card_id and line.startswith(card_id):
                break
            if re.search(r"\b(?:rarity|event|globally\s+catches|added\s*by)\b", line, re.IGNORECASE):
                continue
            anime_name = strip_leading_symbols(line)
            break

    parsed = ParsedText(
        name=name,
        anime_name=anime_name,
        rarity=parse_field(raw, RARITY_PATTERNS) if src.save_rarity else None,
        card_id=card_id,
        command_name=src.command,
        raw_text=raw,
        source_key=src.key,
    )
    return finalize_parsed_text(parsed)


def parse_capture_or_seizer_message(message: Message, src: SourceDef) -> ParsedText:
    # First try label style: New Waifu Added / Name Anime Rarity ID.
    label = parse_label_message(message, src)
    if label.name and label.card_id:
        return label
    # Then try OwO or New Character Added with anime above and ID:name line.
    owo = parse_owo_message(message, src, mode="colon")
    if owo.name and owo.card_id:
        return owo
    return label


def parse_grab_label_message(message: Message, src: SourceDef) -> ParsedText:
    return parse_label_message(message, src)


def parse_smash_message(message: Message, src: SourceDef) -> ParsedText:
    raw = get_combined_message_text(message)
    lines = lines_from_text(raw)
    useful: list[str] = []
    for line in lines:
        if re.search(r"\b(?:rarity|global\s+owners|owners)\b", line, re.IGNORECASE):
            continue
        if re.search(r"(?:\bID\b|🆔)", line, re.IGNORECASE):
            continue
        useful.append(strip_leading_symbols(line))
    parsed = ParsedText(
        name=useful[0] if len(useful) >= 1 else None,
        anime_name=useful[1] if len(useful) >= 2 else None,
        rarity=parse_field(raw, RARITY_PATTERNS),
        card_id=parse_field(raw, [SMASH_ID_RE]),
        command_name=src.command,
        raw_text=raw,
        source_key=src.key,
    )
    return finalize_parsed_text(parsed)


def parse_waifux_message(message: Message, src: SourceDef) -> ParsedText:
    raw = get_combined_message_text(message)
    parsed = ParsedText(
        name=parse_field(raw, [WAIFUX_NAME_RE]),
        anime_name=parse_field(raw, [WAIFUX_SERIES_RE]),
        rarity=None,
        card_id=parse_field(raw, [WAIFUX_ID_RE]),
        command_name=src.command,
        raw_text=raw,
        source_key=src.key,
    )
    return finalize_parsed_text(parsed)


def parse_caption_text(text: Optional[str]) -> ParsedText:
    raw = normalize_parse_text(text)
    return finalize_parsed_text(
        ParsedText(
            name=parse_field(raw, NAME_PATTERNS),
            anime_name=parse_field(raw, ANIME_PATTERNS),
            rarity=parse_field(raw, RARITY_PATTERNS),
            card_id=parse_field(raw, CARD_ID_PATTERNS),
            command_name=parse_command_name(raw),
            raw_text=raw,
            source_key=None,
        )
    )


def parse_caption_text_from_message(message: Message) -> ParsedText:
    candidates = collect_candidate_texts(message)
    for raw in candidates:
        parsed = parse_caption_text(raw)
        if parsed.name:
            return parsed
    raw = candidates[0] if candidates else ""
    return parse_caption_text(raw)


def parse_source_update(message: Message) -> Optional[SourceUpdate]:
    src = get_inline_source_def(message) or get_forward_source_def(message)
    if not src or src.key != "character_seizer":
        return None
    raw = get_combined_message_text(message)
    if not raw:
        return None

    old_name = parse_field(raw, [RENAME_OLD_NAME_RE])
    new_name = parse_field(raw, [RENAME_NEW_NAME_RE])
    if old_name and new_name:
        return SourceUpdate(src.key, "rename", old_name=old_name, new_name=new_name, raw_text=raw)

    rarity_name = parse_field(raw, [RARITY_UPDATE_NAME_RE])
    new_rarity = parse_field(raw, [RARITY_UPDATE_NEW_RE])
    if rarity_name and new_rarity:
        return SourceUpdate(src.key, "rarity", old_name=rarity_name, new_rarity=new_rarity, raw_text=raw)

    return None


def get_effective_parsed_message(message: Message) -> ParsedText:
    src = get_inline_source_def(message) or get_forward_source_def(message)
    if src:
        if src.parser == "smash":
            return parse_smash_message(message, src)
        if src.parser == "waifux":
            return parse_waifux_message(message, src)
        if src.parser == "owo_space":
            return parse_owo_message(message, src, mode="space")
        if src.parser == "label":
            label = parse_label_message(message, src)
            if label.name or label.card_id:
                return label
            return parse_owo_message(message, src, mode="colon")
        if src.parser in {"capture", "seizer"}:
            return parse_capture_or_seizer_message(message, src)
        return parse_owo_message(message, src, mode="colon")

    parsed = parse_caption_text_from_message(message)
    if parsed.command_name:
        parsed.source_key = get_default_source_key_from_command(parsed.command_name)
    return finalize_parsed_text(parsed)


# -----------------------------------------------------
# DB logic
# -----------------------------------------------------
async def ensure_item_indexes(collection) -> None:
    await collection.create_index("file_unique_id", unique=True, sparse=True)
    await collection.create_index("sha256", unique=True, sparse=True)
    await collection.create_index("media_type")
    await collection.create_index("normalized_name")
    await collection.create_index("command_name")
    await collection.create_index("source_key")
    await collection.create_index("source_bot_key")
    await collection.create_index("card_id")
    await collection.create_index("created_at")


async def ensure_indexes() -> None:
    for src in SOURCE_CONFIGS:
        await ensure_item_indexes(get_source_collection(src.key))
    await ensure_item_indexes(db["items_unknown"])
    await sudo_users.create_index("user_id", unique=True)
    await known_users.create_index("user_id", unique=True)
    await known_users.create_index("username")
    await user_modes.create_index("user_id", unique=True)
    await settings_col.create_index("key", unique=True)


async def count_all_source_documents(filter_query: Optional[dict[str, Any]] = None) -> int:
    filter_query = filter_query or {}
    total = 0
    for src in SOURCE_CONFIGS:
        total += await get_source_collection(src.key).count_documents(filter_query)
    total += await db["items_unknown"].count_documents(filter_query)
    return total


async def count_source_documents(source_key: str, filter_query: Optional[dict[str, Any]] = None) -> int:
    return await get_source_collection(source_key).count_documents(filter_query or {})


async def remember_user(message: Message) -> None:
    user = message.from_user
    if not user:
        return
    await known_users.update_one(
        {"user_id": user.id},
        {"$set": {"user_id": user.id, "username": (user.username or "").lower(), "full_name": clean_value(user.full_name), "updated_at": datetime.now(timezone.utc)}},
        upsert=True,
    )


async def remember_chat(message: Message) -> None:
    await remember_user(message)


async def is_sudo_user(user_id: Optional[int]) -> bool:
    return bool(user_id and await sudo_users.find_one({"user_id": user_id}, {"_id": 1}))


async def can_save(message: Message) -> bool:
    user_id = message.from_user.id if message.from_user else None
    if not user_id:
        return False
    if user_id in OWNER_IDS:
        return True
    return await is_sudo_user(user_id)


async def set_autosave_mode(user_id: int, enabled: bool) -> None:
    await user_modes.update_one(
        {"user_id": user_id},
        {"$set": {"user_id": user_id, "autosave_enabled": enabled, "updated_at": datetime.now(timezone.utc)}},
        upsert=True,
    )


async def get_autosave_mode(user_id: Optional[int]) -> bool:
    if not user_id:
        return False
    row = await user_modes.find_one({"user_id": user_id})
    return bool(row and row.get("autosave_enabled"))


async def set_target_chat_autosave_mode(chat_id: int, enabled: bool, updated_by: int) -> None:
    await settings_col.update_one(
        {"key": f"target_chat_autosave:{chat_id}"},
        {"$set": {"key": f"target_chat_autosave:{chat_id}", "chat_id": chat_id, "enabled": enabled, "updated_by": updated_by, "updated_at": datetime.now(timezone.utc)}},
        upsert=True,
    )


async def get_target_chat_autosave_mode(chat_id: Optional[int]) -> bool:
    if not chat_id:
        return False
    row = await settings_col.find_one({"key": f"target_chat_autosave:{chat_id}"})
    return bool(row and row.get("enabled"))


async def apply_source_update(update: SourceUpdate) -> tuple[bool, str]:
    collection = get_source_collection(update.source_key)
    if update.update_type == "rename" and update.old_name and update.new_name:
        result = await collection.update_one(
            {"normalized_name": normalize_name(update.old_name)},
            {"$set": {"name": clean_value(update.new_name), "normalized_name": normalize_name(update.new_name), "updated_at": datetime.now(timezone.utc), "last_source_update": update.raw_text}},
        )
        if result.modified_count:
            return True, f"Renamed: {update.old_name} → {update.new_name}"
        return False, f"Rename target not found: {update.old_name}"

    if update.update_type == "rarity" and update.old_name and update.new_rarity:
        new_rarity = clean_rarity_value(update.new_rarity)
        result = await collection.update_one(
            {"normalized_name": normalize_name(update.old_name)},
            {"$set": {"rarity": new_rarity, "updated_at": datetime.now(timezone.utc), "last_source_update": update.raw_text}},
        )
        if result.modified_count:
            return True, f"Rarity updated: {update.old_name} → {new_rarity}"
        return False, f"Rarity update target not found: {update.old_name}"

    return False, "Invalid update message"


async def upsert_item(*, meta: MediaMeta, parsed: ParsedText, saved_by: int) -> tuple[dict[str, Any], bool]:
    command_name = clean_command_name(parsed.command_name or DEFAULT_COMMAND)
    source_key = parsed.source_key or get_default_source_key_from_command(command_name)
    src = SOURCE_BY_KEY.get(source_key)
    collection = get_source_collection(source_key)
    rarity_value = clean_value(parsed.rarity or "") if (src is None or src.save_rarity) else ""
    doc = {
        "name": clean_value(parsed.name or ""),
        "normalized_name": normalize_name(parsed.name or ""),
        "anime_name": clean_value(parsed.anime_name or ""),
        "rarity": rarity_value,
        "card_id": clean_value(parsed.card_id or ""),
        "command_name": command_name,
        "source_key": source_key,
        "source_bot_key": source_key,
        "source_collection": collection.name,
        "raw_text": parsed.raw_text,
        "media_type": meta.media_type,
        "file_id": meta.file_id,
        "file_unique_id": meta.file_unique_id,
        "sha256": meta.sha256,
        "phash": meta.phash,
        "frame_hashes": meta.frame_hashes,
        "saved_by": saved_by,
        "updated_at": datetime.now(timezone.utc),
    }
    existing = await collection.find_one({"$or": [{"file_unique_id": meta.file_unique_id}, {"sha256": meta.sha256}]})
    if existing:
        await collection.update_one({"_id": existing["_id"]}, {"$set": doc})
        existing.update(doc)
        return existing, False
    doc["created_at"] = datetime.now(timezone.utc)
    result = await collection.insert_one(doc)
    doc["_id"] = result.inserted_id
    return doc, True


# -----------------------------------------------------
# Media hashing
# -----------------------------------------------------
def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


async def download_file_bytes(bot: Bot, file_id: str) -> bytes:
    tg_file = await bot.get_file(file_id)
    if not tg_file.file_path:
        raise RuntimeError("Telegram did not return file_path")
    buffer = BytesIO()
    await bot.download_file(tg_file.file_path, destination=buffer)
    return buffer.getvalue()


def compute_photo_phash(data: bytes) -> str:
    with Image.open(BytesIO(data)) as img:
        img = img.convert("RGB")
        return str(imagehash.phash(img))


def _frame_to_hash(frame) -> str:
    rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
    image = Image.fromarray(rgb)
    return str(imagehash.phash(image))


def compute_video_hashes(data: bytes) -> list[str]:
    with tempfile.NamedTemporaryFile(suffix=".mp4", delete=True) as tmp:
        tmp.write(data)
        tmp.flush()
        cap = cv2.VideoCapture(tmp.name)
        if not cap.isOpened():
            raise RuntimeError("Failed to open video")
        frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0)
        if frame_count <= 0:
            cap.release()
            raise RuntimeError("Video contains no readable frames")
        targets = sorted({max(0, int(frame_count * 0.2) - 1), max(0, int(frame_count * 0.5) - 1), max(0, int(frame_count * 0.8) - 1)})
        hashes: list[str] = []
        for idx in targets:
            cap.set(cv2.CAP_PROP_POS_FRAMES, idx)
            ok, frame = cap.read()
            if ok and frame is not None:
                hashes.append(_frame_to_hash(frame))
        cap.release()
        if not hashes:
            raise RuntimeError("Could not extract frames from video")
        return hashes


async def get_media_meta(bot: Bot, message: Message) -> MediaMeta:
    media_type, media = extract_media_handle(message)
    if not media_type or not media:
        raise ValueError("Message does not contain supported media")
    raw = await download_file_bytes(bot, media.file_id)
    digest = sha256_hex(raw)
    if media_type == "photo":
        return MediaMeta(media_type="photo", file_id=media.file_id, file_unique_id=media.file_unique_id, sha256=digest, phash=compute_photo_phash(raw))
    return MediaMeta(media_type="video", file_id=media.file_id, file_unique_id=media.file_unique_id, sha256=digest, frame_hashes=compute_video_hashes(raw))


# -----------------------------------------------------
# User/admin helpers
# -----------------------------------------------------
async def resolve_user_reference(message: Message, bot: Bot, raw_arg: Optional[str]) -> Optional[dict[str, Any]]:
    if message.reply_to_message and message.reply_to_message.from_user:
        target = message.reply_to_message.from_user
        return {"user_id": target.id, "username": (target.username or "").lower(), "full_name": clean_value(target.full_name)}
    arg = clean_value(raw_arg or "")
    if not arg:
        return None
    if arg.isdigit():
        known = await known_users.find_one({"user_id": int(arg)})
        return known or {"user_id": int(arg), "username": "", "full_name": ""}
    if arg.startswith("@"):
        username = arg.lstrip("@").lower()
        known = await known_users.find_one({"username": username})
        if known:
            return known
        try:
            chat = await bot.get_chat(arg)
            return {"user_id": chat.id, "username": (getattr(chat, "username", "") or "").lower(), "full_name": clean_value(getattr(chat, "full_name", "") or getattr(chat, "title", "") or "")}
        except Exception:
            return None
    return None


def format_target_user(user_doc: dict[str, Any]) -> str:
    username = user_doc.get("username") or ""
    user_id = user_doc.get("user_id")
    full_name = clean_value(user_doc.get("full_name") or "")
    if username:
        return f"@{username} ({user_id})"
    if full_name:
        return f"{full_name} ({user_id})"
    return str(user_id)


async def set_access(collection, user_doc: dict[str, Any], added_by: int, enabled: bool) -> None:
    if enabled:
        await collection.update_one(
            {"user_id": user_doc["user_id"]},
            {"$set": {"user_id": user_doc["user_id"], "username": user_doc.get("username", ""), "full_name": user_doc.get("full_name", ""), "updated_at": datetime.now(timezone.utc), "updated_by": added_by}},
            upsert=True,
        )
    else:
        await collection.delete_one({"user_id": user_doc["user_id"]})


def build_user_mention_html(user) -> str:
    if not user:
        return "Unknown"
    username = (getattr(user, "username", "") or "").strip()
    full_name = clean_value(getattr(user, "full_name", "") or username or "Unknown")
    if username:
        return f'<a href="https://t.me/{html_escape(username)}">{html_escape(full_name)}</a>'
    user_id = getattr(user, "id", None)
    if user_id:
        return f'<a href="tg://user?id={user_id}">{html_escape(full_name)}</a>'
    return html_escape(full_name)


def build_added_log_caption(*, doc: dict[str, Any], created: bool, mode: str, source_label: str, added_by_user) -> str:
    status = "Saved" if created else "Updated"
    added_by = build_user_mention_html(added_by_user)
    lines = [
        f"{status}",
        f"Name : {html_escape(clean_value(doc.get('name') or 'Unknown'))}",
        f"Anime : {html_escape(clean_value(doc.get('anime_name') or '-'))}",
        f"Rarity : {html_escape(clean_value(doc.get('rarity') or '-'))}",
        f"ID : {html_escape(clean_value(doc.get('card_id') or '-'))}",
        f"Mode: {html_escape(mode)}",
        f"Source: {html_escape(clean_value(doc.get('source_key') or source_label))}",
        f"Collection: <code>{html_escape(clean_value(doc.get('source_collection') or '-'))}</code>",
        f"Cmd: <code>{html_escape(clean_value(doc.get('command_name') or DEFAULT_COMMAND))}</code>",
        "",
        f"Added by {added_by}",
    ]
    return "\n".join(lines)


async def send_added_log(*, bot: Bot, source_message: Message, doc: dict[str, Any], created: bool, mode: str, source_label: str, added_by_user) -> None:
    if not ADDED_LOG_CHANNEL:
        return
    media_type, media = extract_media_handle(source_message)
    if not media_type or not media:
        return
    caption = build_added_log_caption(doc=doc, created=created, mode=mode, source_label=source_label, added_by_user=added_by_user)
    if media_type == "photo":
        await bot.send_photo(chat_id=ADDED_LOG_CHANNEL, photo=media.file_id, caption=caption, parse_mode=ParseMode.HTML)
    else:
        await bot.send_video(chat_id=ADDED_LOG_CHANNEL, video=media.file_id, caption=caption, parse_mode=ParseMode.HTML)


# -----------------------------------------------------
# Status / UI text
# -----------------------------------------------------
def build_start_text() -> str:
    return (
        "🛠 Adding Bot Ready\n\n"
        "Source တစ်ခုချင်း collection ခွဲသိမ်းတဲ့ version ဖြစ်ပါတယ်။\n\n"
        "Available:\n"
        "• /autosave on|off|status\n"
        "• /save (reply media)\n"
        "• /status\n"
        "• /stats\n"
        "• /addsudo /rmsudo\n\n"
        "Target chat မှာ save-only mode သုံးမယ်ဆို /autosave on လုပ်ပါ။"
    )


async def build_status_text() -> str:
    total_media = await count_all_source_documents({})
    photos = await count_all_source_documents({"media_type": "photo"})
    videos = await count_all_source_documents({"media_type": "video"})
    sudo_count = await sudo_users.count_documents({})
    users = await known_users.count_documents({})
    per_bot = []
    for idx, src in enumerate(SOURCE_CONFIGS, start=1):
        count = await count_source_documents(src.key)
        per_bot.append(f"{idx}. {html_escape(src.bot_username)} / <code>{html_escape(src.command)}</code> → <code>{html_escape(src.collection)}</code> : <b>{count}</b>")
    lines = [
        "🛠 <b>ADDING BOT STATUS</b>",
        f"‣ DB Name : <code>{html_escape(DB_NAME)}</code>",
        f"‣ Total Media : <b>{total_media}</b>",
        f"‣ Photos : <b>{photos}</b>",
        f"‣ Videos : <b>{videos}</b>",
        f"‣ Known Users : <b>{users}</b>",
        f"‣ Sudo Users : <b>{sudo_count}</b>",
        f"‣ Target Chat : <code>{html_escape(str(DEFAULT_TARGET_CHAT or '-'))}</code>",
        f"‣ Added Log Channel : <code>{html_escape(ADDED_LOG_CHANNEL or '-')}</code>",
        f"‣ Mode : <b>{'WEBHOOK' if USE_WEBHOOK else 'POLLING'}</b>",
        "",
        "🤖 <b>Source Collections</b>",
        *per_bot,
    ]
    return "\n".join(lines)


async def delayed_pm2_restart(delay_seconds: float = 1.5) -> None:
    await asyncio.sleep(delay_seconds)

    cmd = [PM2_BIN, "restart", PM2_PROCESS_NAME, "--update-env"]
    logger.warning("Telegram restart requested. Running: %s", " ".join(shlex.quote(x) for x in cmd))

    try:
        process = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        stdout, stderr = await process.communicate()
        logger.warning(
            "PM2 restart finished | returncode=%s | stdout=%s | stderr=%s",
            process.returncode,
            stdout.decode(errors="ignore")[:1000],
            stderr.decode(errors="ignore")[:1000],
        )
    except Exception:
        logger.exception("PM2 restart command failed")


# -----------------------------------------------------
# Handlers
# -----------------------------------------------------
@router.message(Command("start"))
async def start_handler(message: Message) -> None:
    await remember_chat(message)
    if not await can_save(message):
        await message.reply("ဒီ adding bot ကို owner / sudo only သုံးလို့ရပါတယ်။")
        return
    await message.reply(build_start_text())


@router.message(Command("status"))
async def status_handler(message: Message) -> None:
    await remember_chat(message)
    if not await can_save(message):
        return
    await message.reply(await build_status_text(), parse_mode=ParseMode.HTML)


@router.message(Command("stats"))
async def stats_handler(message: Message) -> None:
    await status_handler(message)


@router.message(Command("restart"))
async def restart_handler(message: Message) -> None:
    await remember_chat(message)

    user_id = message.from_user.id if message.from_user else None
    if user_id not in OWNER_IDS:
        return

    if not ENABLE_TELEGRAM_RESTART:
        await message.reply(
            "Telegram restart is disabled.\n\n"
            "Enable with:\n"
            "<code>ENABLE_TELEGRAM_RESTART=true</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    await message.reply(
        "♻️ Restarting bot with PM2...\n"
        f"Process: <code>{html_escape(PM2_PROCESS_NAME)}</code>",
        parse_mode=ParseMode.HTML,
    )

    asyncio.create_task(delayed_pm2_restart())


@router.message(Command("addsudo"))
async def addsudo_handler(message: Message, command: CommandObject, bot: Bot) -> None:
    await remember_chat(message)
    if not message.from_user or message.from_user.id not in OWNER_IDS:
        return
    target = await resolve_user_reference(message, bot, command.args)
    if not target:
        await message.reply("အသုံးပြုပုံ:\nReply + /addsudo\n/addsudo @username\n/addsudo 123456789")
        return
    await set_access(sudo_users, target, message.from_user.id, True)
    await message.reply(f"Sudo added: <b>{html_escape(format_target_user(target))}</b>", parse_mode=ParseMode.HTML)


@router.message(Command("rmsudo"))
async def rmsudo_handler(message: Message, command: CommandObject, bot: Bot) -> None:
    await remember_chat(message)
    if not message.from_user or message.from_user.id not in OWNER_IDS:
        return
    target = await resolve_user_reference(message, bot, command.args)
    if not target:
        await message.reply("အသုံးပြုပုံ:\nReply + /rmsudo\n/rmsudo @username\n/rmsudo 123456789")
        return
    await set_access(sudo_users, target, message.from_user.id, False)
    await message.reply(f"Sudo removed: <b>{html_escape(format_target_user(target))}</b>", parse_mode=ParseMode.HTML)


@router.message(Command("autosave"))
async def autosave_handler(message: Message, command: CommandObject) -> None:
    await remember_chat(message)
    if not (is_private_chat(message) or is_default_target_chat(message)):
        await message.reply("ဒီ command ကို DM/private chat (or) target chat ထဲမှာပဲ သုံးပါ။")
        return
    if not await can_save(message):
        return
    arg = clean_value(command.args or "").lower()
    if arg not in {"on", "off", "status"}:
        await message.reply("အသုံးပြုပုံ:\n/autosave on\n/autosave off\n/autosave status")
        return
    if is_default_target_chat(message):
        chat_id = message.chat.id
        if arg == "status":
            enabled = await get_target_chat_autosave_mode(chat_id)
            await message.reply(f"Target Chat Auto-save mode: <b>{'ON' if enabled else 'OFF'}</b>", parse_mode=ParseMode.HTML)
            return
        enabled = arg == "on"
        await set_target_chat_autosave_mode(chat_id, enabled, message.from_user.id)
        await message.reply(f"Target Chat Auto-save mode: <b>{'ON' if enabled else 'OFF'}</b>", parse_mode=ParseMode.HTML)
        return
    user_id = message.from_user.id
    if arg == "status":
        enabled = await get_autosave_mode(user_id)
        await message.reply(f"Auto-save mode: <b>{'ON' if enabled else 'OFF'}</b>", parse_mode=ParseMode.HTML)
        return
    enabled = arg == "on"
    await set_autosave_mode(user_id, enabled)
    await message.reply(f"Auto-save mode: <b>{'ON' if enabled else 'OFF'}</b>", parse_mode=ParseMode.HTML)


async def process_source_update_if_any(message: Message) -> bool:
    update = parse_source_update(message)
    if not update:
        return False
    ok, text = await apply_source_update(update)
    prefix = "✅" if ok else "⚠️"
    await message.reply(f"{prefix} {html_escape(text)}", parse_mode=ParseMode.HTML)
    return True


@router.message(Command("save"))
async def save_handler(message: Message, command: CommandObject, bot: Bot) -> None:
    await remember_chat(message)
    if not await can_save(message):
        return
    target = message.reply_to_message or message
    if await process_source_update_if_any(target):
        return
    media_type, _media = extract_media_handle(target)
    if not media_type:
        await message.reply("/save ကို media message ကို reply ပြီးသုံးပါ")
        return
    parsed = get_effective_parsed_message(target)
    if command.args:
        parsed.name = clean_value(command.args)
    if not parsed.name:
        await message.reply("name မတွေ့ပါ။\nအသုံးပြုပုံ: replied media ပေါ်မှာ /save Nahida")
        return
    try:
        meta = await get_media_meta(bot, target)
        doc, created = await upsert_item(meta=meta, parsed=parsed, saved_by=message.from_user.id)
    except Exception as exc:
        logger.exception("save failed")
        await message.reply(f"save မအောင်မြင်ပါ: {html_escape(str(exc))}", parse_mode=ParseMode.HTML)
        return
    try:
        await send_added_log(bot=bot, source_message=target, doc=doc, created=created, mode="manual-save", source_label=get_log_source_label(target), added_by_user=message.from_user)
    except Exception:
        logger.exception("added log send failed")
    status = "Saved" if created else "Updated"
    await message.reply(
        f"{status}: <b>{html_escape(doc['name'])}</b>\n"
        f"ID: <b>{html_escape(doc.get('card_id') or '-')}</b>\n"
        f"Type: <b>{doc['media_type']}</b>\n"
        f"Source: <code>{html_escape(doc.get('source_key') or '-')}</code>\n"
        f"Collection: <code>{html_escape(doc.get('source_collection') or '-')}</code>\n"
        f"Cmd: <code>{html_escape(doc['command_name'])}</code>",
        parse_mode=ParseMode.HTML,
    )


async def autosave_media(message: Message, bot: Bot, mode: str) -> None:
    if await process_source_update_if_any(message):
        return
    parsed = get_effective_parsed_message(message)
    if not parsed.name:
        await message.reply("name မတွေ့ပါ။ supported post ကို forward / send လုပ်ပါ။")
        return
    try:
        meta = await get_media_meta(bot, message)
        doc, created = await upsert_item(meta=meta, parsed=parsed, saved_by=(message.from_user.id if message.from_user else 0))
        source_label = get_autosave_source_label(message)
        try:
            await send_added_log(bot=bot, source_message=message, doc=doc, created=created, mode=mode, source_label=str(source_label), added_by_user=message.from_user)
        except Exception:
            logger.exception("added log send failed")
        status = "Saved" if created else "Updated"
        await message.reply(
            f"{status}: <b>{html_escape(doc['name'])}</b>\n"
            f"ID: <b>{html_escape(doc.get('card_id') or '-')}</b>\n"
            f"Mode: <b>{html_escape(mode)}</b>\n"
            f"Source: <code>{html_escape(doc.get('source_key') or '-')}</code>\n"
            f"Collection: <code>{html_escape(doc.get('source_collection') or '-')}</code>\n"
            f"Cmd: <code>{html_escape(doc['command_name'])}</code>",
            parse_mode=ParseMode.HTML,
        )
    except Exception as exc:
        logger.exception("auto-save failed")
        await message.reply(f"auto-save error: {html_escape(str(exc))}", parse_mode=ParseMode.HTML)


@router.message(F.photo | F.video | F.animation | F.document)
async def media_handler(message: Message, bot: Bot) -> None:
    await remember_chat(message)
    media_type, _media = extract_media_handle(message)
    if not media_type:
        return
    user_can_save = await can_save(message)
    user_id = message.from_user.id if message.from_user else None
    autosave_enabled = await get_autosave_mode(user_id)
    supported_source = bool(is_allowed_forward_source(message) or get_inline_source_command(message))

    if is_default_target_chat(message):
        target_chat_autosave_enabled = await get_target_chat_autosave_mode(message.chat.id)
        if not target_chat_autosave_enabled:
            return
        if not supported_source:
            return
        await autosave_media(message, bot, "target-auto-save")
        return

    if is_private_chat(message) and user_can_save and autosave_enabled:
        if not supported_source:
            if is_forwarded_message(message):
                await message.reply("ဒီ forwarded source ကို auto-save ခွင့်မပြုထားသေးပါဘူး။")
            return
        await autosave_media(message, bot, "auto-save")
        return


# -----------------------------------------------------
# Webhook / runner
# -----------------------------------------------------
def normalize_webhook_path(path: str) -> str:
    return path if path.startswith("/") else f"/{path}"


async def on_startup(bot: Bot) -> None:
    await ensure_indexes()
    await bot.set_my_commands(
        [
            BotCommand(command="start", description="Start the adding bot"),
            BotCommand(command="status", description="Show adding bot status"),
            BotCommand(command="stats", description="Show adding bot stats"),
            BotCommand(command="autosave", description="Auto-save on/off/status"),
            BotCommand(command="restart", description="Restart bot with PM2"),
        ]
    )
    me = await bot.get_me()
    logger.info("Bot started as @%s", me.username)
    logger.info("DB_NAME: %s", DB_NAME)
    logger.info("Source collections: %s", {src.key: src.collection for src in SOURCE_CONFIGS})
    logger.info("Inline usernames: %s", sorted(SOURCE_BY_INLINE_USERNAME.keys()))
    logger.info("Forward usernames: %s", sorted(SOURCE_BY_FORWARD_USERNAME.keys()))
    logger.info("Forward titles: %s", sorted(SOURCE_BY_FORWARD_TITLE.keys()))
    logger.info("Added log channel: %s", ADDED_LOG_CHANNEL or "none")
    logger.info("Default target chat: %s", DEFAULT_TARGET_CHAT if DEFAULT_TARGET_CHAT is not None else "none")
    logger.info("Mode: %s", "WEBHOOK" if USE_WEBHOOK else "POLLING")


async def health_handler(_request: web.Request) -> web.Response:
    return web.json_response({"ok": True, "service": "adding-bot", "db": DB_NAME, "mode": "webhook" if USE_WEBHOOK else "polling"})


async def start_web_app(dp: Dispatcher, bot: Bot):
    app = web.Application()
    app.router.add_get("/", health_handler)
    app.router.add_get("/healthz", health_handler)

    if USE_WEBHOOK:
        webhook_path = normalize_webhook_path(WEBHOOK_PATH)
        SimpleRequestHandler(dispatcher=dp, bot=bot, secret_token=WEBHOOK_SECRET).register(app, path=webhook_path)
        setup_application(app, dp, bot=bot)

    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", PORT)
    await site.start()

    if USE_WEBHOOK:
        webhook_url = f"{PUBLIC_URL.rstrip('/')}{normalize_webhook_path(WEBHOOK_PATH)}"
        await bot.set_webhook(url=webhook_url, secret_token=WEBHOOK_SECRET, drop_pending_updates=False)
        logger.info("Webhook set to %s", webhook_url)

    return runner


# -----------------------------------------------------
# Add Helper Userbot (optional)
# -----------------------------------------------------
# Enable with ADD_HELPER_ENABLED=true. It uses a Pyrogram user session to send
# inline results / forward source-channel posts into DEFAULT_TARGET_CHAT so this
# adding bot can auto-save them.

ADD_HELPER_ENABLED = os.getenv("ADD_HELPER_ENABLED", "false").lower() == "true"
ADD_HELPER_API_ID = int(os.getenv("API_ID", "0") or 0)
ADD_HELPER_API_HASH = os.getenv("API_HASH", "").strip()
ADD_HELPER_SESSION_STRING = os.getenv("SESSION_STRING", "").strip()
ADD_HELPER_DEFAULT_SEND_DELAY = int(os.getenv("DEFAULT_SEND_DELAY", "5"))
ADD_HELPER_MAX_SEND_DELAY = int(os.getenv("MAX_SEND_DELAY", "30"))
ADD_HELPER_MAX_RETRIES = int(os.getenv("MAX_RETRIES", "5"))
ADD_HELPER_RETRY_BASE_DELAY = int(os.getenv("RETRY_BASE_DELAY", "3"))
ADD_HELPER_CONTROL_POLL_INTERVAL = float(os.getenv("CONTROL_POLL_INTERVAL", "2"))
ADD_HELPER_CONTROL_HISTORY_LIMIT = int(os.getenv("CONTROL_HISTORY_LIMIT", "25"))
ADD_HELPER_STATE_FILE = os.getenv("STATE_FILE", "seeder_state.json").strip() or "seeder_state.json"
ADD_HELPER_CLEAR_STATE_ON_FINISH = os.getenv("CLEAR_STATE_ON_FINISH", "true").lower() == "true"
ADD_HELPER_SESSIONS_DIR = os.getenv("SESSIONS_DIR", "sessions").strip() or "sessions"
ADD_HELPER_STARTUP_MESSAGE = os.getenv("ADD_HELPER_STARTUP_MESSAGE", "true").lower() == "true"

ADD_HELPER_INLINE_OVERRIDES = {
    "character_catcher": os.getenv("CATCHER_INLINE_BOT", "@Character_Catcher_Bot"),
    "character_seizer": os.getenv("SEIZER_INLINE_BOT", "@Character_Seizer_Bot"),
    "capture_character": os.getenv("CAPTURE_INLINE_BOT", "@CaptureCharacterBot"),
    "takers_character": os.getenv("TAKERS_INLINE_BOT", "@Takers_character_bot"),
    "grab_your_waifu": os.getenv("GRAB_INLINE_BOT", "@Grab_Your_Waifu_Bot"),
}
ADD_HELPER_FORWARD_OVERRIDES = {
    "character_seizer": os.getenv("FW_SEIZER_SOURCE_CHAT", "@Seizer_Database"),
    "capture_character": os.getenv("FW_CAPTURE_SOURCE_CHAT", "@CaptureDatabase"),
    "characters_hallow": os.getenv("FW_HALLOW_SOURCE_CHAT", "@hallowuploads"),
}


@dataclass(frozen=True)
class AddHelperSource:
    key: str
    title: str
    inline_bot: str
    start_aliases: tuple[str, ...]
    resume_aliases: tuple[str, ...]
    forward_chat: str = ""
    forward_start_aliases: tuple[str, ...] = ()
    forward_resume_aliases: tuple[str, ...] = ()


def _env_inline(key: str, default_bot: str) -> str:
    env_key = f"INLINE_{key.upper()}"
    return os.getenv(env_key, ADD_HELPER_INLINE_OVERRIDES.get(key, default_bot)).strip() or default_bot


def _env_forward(key: str, default_chat: str) -> str:
    env_key = f"FW_{key.upper()}"
    return os.getenv(env_key, ADD_HELPER_FORWARD_OVERRIDES.get(key, default_chat)).strip() or default_chat


ADD_HELPER_SOURCES: list[AddHelperSource] = [
    AddHelperSource("character_catcher", "Character Catcher", _env_inline("character_catcher", "@Character_Catcher_Bot"), ("/startcatcherbot", "/startcharactercatcher", "/start_character_catcher"), ("/resumecatcherbot", "/resumecharactercatcher", "/resume_character_catcher")),
    AddHelperSource("characters_hallow", "Characters Hallow", _env_inline("characters_hallow", "@Characters_Hallow_bot"), ("/starthallowbot", "/starthallow", "/start_hallow"), ("/resumehallowbot", "/resumehallow", "/resume_hallow"), _env_forward("characters_hallow", "@hallowuploads"), ("/startfwhallowbot", "/startfwhallow", "/start_fw_hallow"), ("/resumefwhallowbot", "/resumefwhallow", "/resume_fw_hallow")),
    AddHelperSource("capture_character", "Capture Character", _env_inline("capture_character", "@CaptureCharacterBot"), ("/startcapturebot", "/startcapture", "/start_capture"), ("/resumecapturebot", "/resumecapture", "/resume_capture"), _env_forward("capture_character", "@CaptureDatabase"), ("/startfwcapturebot", "/startfwcapture", "/start_fw_capture"), ("/resumefwcapturebot", "/resumefwcapture", "/resume_fw_capture")),
    AddHelperSource("character_seizer", "Character Seizer", _env_inline("character_seizer", "@Character_Seizer_Bot"), ("/startseizerbot", "/startseizer", "/start_seizer"), ("/resumeseizerbot", "/resumeseizer", "/resume_seizer"), _env_forward("character_seizer", "@Seizer_Database"), ("/startfwseizerbot", "/startfwseizer", "/start_fw_seizer"), ("/resumefwseizerbot", "/resumefwseizer", "/resume_fw_seizer")),
    AddHelperSource("husbando_grabber", "Husbando Grabber", _env_inline("husbando_grabber", "@Husbando_Grabber_Bot"), ("/starthusbandograbberbot", "/starthusbandograbber", "/start_husbando_grabber"), ("/resumehusbandograbberbot", "/resumehusbandograbber", "/resume_husbando_grabber")),
    AddHelperSource("grab_your_waifu", "Grab Your Waifu", _env_inline("grab_your_waifu", "@Grab_Your_Waifu_Bot"), ("/startgrabbot", "/startgrabyourwaifu", "/start_grab_your_waifu"), ("/resumegrabbot", "/resumegrabyourwaifu", "/resume_grab_your_waifu")),
    AddHelperSource("grab_your_husbando", "Grab Your Husbando", _env_inline("grab_your_husbando", "@Grab_Your_Husbando_Bot"), ("/startgrabyourhusbandobot", "/startgrabyourhusbando", "/start_grab_your_husbando"), ("/resumegrabyourhusbandobot", "/resumegrabyourhusbando", "/resume_grab_your_husbando")),
    AddHelperSource("takers_character", "Takers Character", _env_inline("takers_character", "@Takers_character_bot"), ("/starttakersbot", "/starttakers", "/start_takers"), ("/resumetakersbot", "/resumetakers", "/resume_takers")),
    AddHelperSource("catch_your_husbando", "Catch Your Husbando", _env_inline("catch_your_husbando", "@Catch_Your_Husbando_Bot"), ("/startcatchyourhusbandobot", "/startcatchyourhusbando", "/start_catch_your_husbando"), ("/resumecatchyourhusbandobot", "/resumecatchyourhusbando", "/resume_catch_your_husbando")),
    AddHelperSource("smash_character", "Smash Character", _env_inline("smash_character", "@Smash_Character_Bot"), ("/startsmashbot", "/startsmash", "/start_smash"), ("/resumesmashbot", "/resumesmash", "/resume_smash")),
    AddHelperSource("waifux_grab", "Waifux Grab", _env_inline("waifux_grab", "@WaifuxGrabBot"), ("/startwaifuxgrabbot", "/startwaifuxgrab", "/startwaifux", "/start_waifux"), ("/resumewaifuxgrabbot", "/resumewaifuxgrab", "/resumewaifux", "/resume_waifux")),
    AddHelperSource("catch_your_waifu", "Catch Your Waifu", _env_inline("catch_your_waifu", "@Catch_Your_Waifu_Bot"), ("/startcatchyourwaifubot", "/startcatchyourwaifu", "/start_catch_your_waifu"), ("/resumecatchyourwaifubot", "/resumecatchyourwaifu", "/resume_catch_your_waifu")),
    AddHelperSource("waifu_grabber", "Waifu Grabber", _env_inline("waifu_grabber", "@Waifu_Grabber_Bot"), ("/startwaifugrabberbot", "/startwaifugrabber", "/start_waifu_grabber"), ("/resumewaifugrabberbot", "/resumewaifugrabber", "/resume_waifu_grabber")),
]

ADD_HELPER_START_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_RESUME_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_FW_START_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_FW_RESUME_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_FW_VIDEO_START_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_FW_VIDEO_RESUME_COMMANDS: dict[str, AddHelperSource] = {}
for _src in ADD_HELPER_SOURCES:
    for _cmd in _src.start_aliases:
        ADD_HELPER_START_COMMANDS[_cmd] = _src
    for _cmd in _src.resume_aliases:
        ADD_HELPER_RESUME_COMMANDS[_cmd] = _src
    for _cmd in _src.forward_start_aliases:
        ADD_HELPER_FW_START_COMMANDS[_cmd] = _src
    for _cmd in _src.forward_resume_aliases:
        ADD_HELPER_FW_RESUME_COMMANDS[_cmd] = _src
    if _src.forward_chat and _src.forward_start_aliases:
        for _cmd in _src.forward_start_aliases:
            base = _cmd.replace("/startfw", "/startfwvideo", 1)
            ADD_HELPER_FW_VIDEO_START_COMMANDS[base] = _src
            ADD_HELPER_FW_VIDEO_START_COMMANDS[_cmd.replace("bot", "videobot")] = _src
        for _cmd in _src.forward_resume_aliases:
            base = _cmd.replace("/resumefw", "/resumefwvideo", 1)
            ADD_HELPER_FW_VIDEO_RESUME_COMMANDS[base] = _src
            ADD_HELPER_FW_VIDEO_RESUME_COMMANDS[_cmd.replace("bot", "videobot")] = _src


def add_helper_clean(value: str) -> str:
    return " ".join((value or "").split()).strip()


def add_helper_command_name(text: str) -> str:
    text = add_helper_clean(text)
    return text.split()[0].lower() if text else ""


def add_helper_parse_delay(text: str, default_delay: int) -> int:
    parts = add_helper_clean(text).split()
    if len(parts) < 2:
        return default_delay
    if not parts[1].isdigit():
        raise ValueError("Delay must be a number")
    return int(parts[1])


def add_helper_parse_resume(text: str, default_delay: int) -> tuple[int, int]:
    parts = add_helper_clean(text).split()
    if len(parts) < 2 or not parts[1].isdigit():
        raise ValueError("Resume count is required. Example: /resumegrabbot 1000 5")
    count = int(parts[1])
    delay = default_delay
    if len(parts) >= 3:
        if not parts[2].isdigit():
            raise ValueError("Delay must be a number")
        delay = int(parts[2])
    return count, delay


def add_helper_state_path():
    from pathlib import Path
    return Path(ADD_HELPER_STATE_FILE)


def add_helper_load_state() -> dict[str, Any]:
    import json
    path = add_helper_state_path()
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        logger.exception("AddHelper failed to read state file")
        return {}


def add_helper_save_state(data: dict[str, Any]) -> None:
    import json
    try:
        add_helper_state_path().write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        logger.exception("AddHelper failed to write state file")


def add_helper_clear_progress() -> None:
    data = add_helper_load_state()
    for key in ["runner_mode", "source_ref", "target_chat", "current_offset", "current_index", "sent_count", "delay_seconds", "resume_target_count"]:
        data.pop(key, None)
    add_helper_save_state(data)


def add_helper_get_control_last_msg_id() -> int:
    return int(add_helper_load_state().get("control_last_msg_id") or 0)


def add_helper_set_control_last_msg_id(message_id: int) -> None:
    data = add_helper_load_state()
    data["control_last_msg_id"] = int(message_id)
    add_helper_save_state(data)


@dataclass
class AddHelperRunnerState:
    running: bool = False
    runner_mode: str = "inline"
    sent_count: int = 0
    delay_seconds: int = ADD_HELPER_DEFAULT_SEND_DELAY
    target_chat: str | int | None = None
    current_offset: str = ""
    current_index: int = 0
    last_error: str = ""
    source_ref: str = ""
    resume_target_count: int = 0


class AddHelperService:
    def __init__(self):
        self.enabled = ADD_HELPER_ENABLED
        self.client = None
        self.runner_task: Optional[asyncio.Task] = None
        self.control_task: Optional[asyncio.Task] = None
        self.stop_event = asyncio.Event()
        self.runner_stop_event = asyncio.Event()
        self.state = AddHelperRunnerState(target_chat=DEFAULT_TARGET_CHAT)
        self.resolved_target_chat: str | int | None = DEFAULT_TARGET_CHAT

    def is_running(self) -> bool:
        return self.runner_task is not None and not self.runner_task.done()

    def _validate_config(self) -> None:
        if not self.enabled:
            return
        if not ADD_HELPER_API_ID:
            raise RuntimeError("API_ID is required when ADD_HELPER_ENABLED=true")
        if not ADD_HELPER_API_HASH:
            raise RuntimeError("API_HASH is required when ADD_HELPER_ENABLED=true")
        if not ADD_HELPER_SESSION_STRING:
            raise RuntimeError("SESSION_STRING is required when ADD_HELPER_ENABLED=true")
        if DEFAULT_TARGET_CHAT is None:
            raise RuntimeError("DEFAULT_TARGET_CHAT is required when ADD_HELPER_ENABLED=true")

    async def start(self) -> None:
        if not self.enabled:
            logger.info("AddHelper disabled")
            return
        self._validate_config()
        from pathlib import Path
        from pyrogram import Client as PyroClient
        Path(ADD_HELPER_SESSIONS_DIR).mkdir(parents=True, exist_ok=True)
        self.client = PyroClient(name="addingbot_add_helper_userbot", api_id=ADD_HELPER_API_ID, api_hash=ADD_HELPER_API_HASH, session_string=ADD_HELPER_SESSION_STRING, workdir=ADD_HELPER_SESSIONS_DIR)
        await self.client.start()
        await self._warmup_peers()
        await self._initialize_control_cursor()
        if ADD_HELPER_STARTUP_MESSAGE:
            try:
                await self.client.send_message(self.resolved_target_chat, "AddHelper online ✅")
            except Exception:
                logger.exception("AddHelper startup message failed")
        self.stop_event = asyncio.Event()
        self.control_task = asyncio.create_task(self._control_loop())
        me = await self.client.get_me()
        logger.info("AddHelper user session started as %s (%s)", me.first_name, me.id)

    async def stop(self) -> None:
        self.stop_event.set()
        if self.is_running():
            await self.stop_runner()
        if self.control_task:
            self.control_task.cancel()
            try:
                await self.control_task
            except asyncio.CancelledError:
                pass
            except Exception:
                logger.exception("AddHelper control task stop failed")
        if self.client:
            try:
                await self.client.stop()
            except Exception:
                logger.exception("AddHelper client stop failed")

    async def _warmup_peers(self) -> None:
        try:
            async for dialog in self.client.get_dialogs():
                _ = dialog.chat.id
            logger.info("AddHelper dialogs warmup completed")
        except Exception as e:
            logger.warning("AddHelper dialogs warmup failed: %s", e)
        try:
            chat = await self.client.get_chat(DEFAULT_TARGET_CHAT)
            self.resolved_target_chat = chat.id
            self.state.target_chat = chat.id
            title = getattr(chat, "title", None) or getattr(chat, "first_name", None) or ""
            logger.info("AddHelper target chat resolved: %s (%s)", title, chat.id)
        except Exception as e:
            raise RuntimeError("DEFAULT_TARGET_CHAT ကို user session က resolve မလုပ်နိုင်သေးပါ။ user account ကို target group ထဲ join ထားပြီး group ကိုတစ်ခါဖွင့်၊ message တစ်ခါပို့ပြီးမှ ပြန် run ပါ။") from e

    async def _initialize_control_cursor(self) -> None:
        if add_helper_get_control_last_msg_id() > 0:
            logger.info("AddHelper control cursor restored")
            return
        latest_id = 0
        async for msg in self.client.get_chat_history(self.resolved_target_chat, limit=1):
            latest_id = int(msg.id)
            break
        if latest_id > 0:
            add_helper_set_control_last_msg_id(latest_id)
            logger.info("AddHelper control cursor initialized at %s", latest_id)

    async def _reply(self, text: str, reply_to_message_id: Optional[int] = None) -> None:
        await self.client.send_message(self.resolved_target_chat, text, reply_to_message_id=reply_to_message_id)

    def _is_owner_or_self(self, msg) -> bool:
        if getattr(msg, "outgoing", False):
            return True
        if not getattr(msg, "from_user", None):
            return False
        return msg.from_user.id in OWNER_IDS

    def _load_progress(self, runner_mode: str, source_ref: str) -> tuple[str, int, int, int]:
        data = add_helper_load_state()
        if data.get("runner_mode") != runner_mode or data.get("source_ref") != source_ref:
            return "", 0, 0, 0
        return str(data.get("current_offset") or ""), int(data.get("current_index") or 0), int(data.get("sent_count") or 0), int(data.get("resume_target_count") or data.get("sent_count") or 0)

    def _save_progress(self, source_ref: str, offset: str, index: int) -> None:
        data = add_helper_load_state()
        data.update({"runner_mode": self.state.runner_mode, "source_ref": source_ref, "target_chat": str(self.resolved_target_chat), "current_offset": offset, "current_index": index, "sent_count": self.state.sent_count, "delay_seconds": self.state.delay_seconds, "resume_target_count": self.state.resume_target_count})
        add_helper_save_state(data)

    async def stop_runner(self) -> bool:
        if not self.is_running():
            return False
        self.runner_stop_event.set()
        try:
            await self.runner_task
        except Exception:
            logger.exception("AddHelper runner stopped with error")
        finally:
            self.runner_task = None
            self.state.running = False
        return True

    async def _sleep_with_stop(self, seconds: float):
        if seconds <= 0:
            return
        try:
            await asyncio.wait_for(self.runner_stop_event.wait(), timeout=seconds)
        except asyncio.TimeoutError:
            pass

    def _backoff_delay(self, attempt: int) -> int:
        return ADD_HELPER_RETRY_BASE_DELAY * (2 ** max(0, attempt - 1))

    async def _get_inline_results(self, source_bot: str, offset: str):
        from pyrogram.errors import FloodWait, RPCError
        last_exc = None
        for attempt in range(1, ADD_HELPER_MAX_RETRIES + 1):
            if self.runner_stop_event.is_set():
                raise asyncio.CancelledError()
            try:
                return await self.client.get_inline_bot_results(bot=source_bot, query="", offset=offset)
            except FloodWait as e:
                wait_for = int(getattr(e, "value", getattr(e, "x", 5)))
                self.state.last_error = f"FloodWait(get_results): {wait_for}s"
                await self._sleep_with_stop(wait_for + 1)
                last_exc = e
            except (RPCError, OSError, TimeoutError) as e:
                self.state.last_error = f"get_results retry error: {e}"
                last_exc = e
                if attempt < ADD_HELPER_MAX_RETRIES:
                    await self._sleep_with_stop(self._backoff_delay(attempt))
        raise RuntimeError(f"get_inline_bot_results failed: {last_exc}")

    async def _send_inline_result(self, source_bot: str, results, result_id: str):
        from pyrogram.errors import FloodWait, RPCError
        last_exc = None
        for attempt in range(1, ADD_HELPER_MAX_RETRIES + 1):
            if self.runner_stop_event.is_set():
                raise asyncio.CancelledError()
            try:
                await self.client.send_inline_bot_result(chat_id=self.resolved_target_chat, query_id=results.query_id, result_id=result_id)
                return
            except FloodWait as e:
                wait_for = int(getattr(e, "value", getattr(e, "x", 5)))
                self.state.last_error = f"FloodWait(send_result): {wait_for}s"
                await self._sleep_with_stop(wait_for + 1)
                last_exc = e
            except (RPCError, OSError, TimeoutError, ValueError) as e:
                self.state.last_error = f"send_result retry error: {e}"
                last_exc = e
                if attempt < ADD_HELPER_MAX_RETRIES:
                    await self._sleep_with_stop(self._backoff_delay(attempt))
        raise RuntimeError(f"send_inline_bot_result failed: {last_exc}")

    async def _locate_inline_cursor(self, source_bot: str, resume_count: int) -> tuple[str, int]:
        if resume_count <= 0:
            return "", 0
        offset = ""
        seen = 0
        while True:
            results = await self._get_inline_results(source_bot, offset)
            page_len = len(results.results)
            if page_len <= 0:
                raise RuntimeError("No inline results found")
            if seen + page_len > resume_count:
                return offset, resume_count - seen
            seen += page_len
            offset = results.next_offset or ""
            if not offset:
                raise RuntimeError(f"Resume count {resume_count} exceeds available inline results ({seen})")

    async def start_inline(self, source_bot: str, delay_seconds: int, resume_count: Optional[int] = None):
        if self.is_running():
            raise RuntimeError("AddHelper is already running")
        delay_seconds = max(1, min(delay_seconds, ADD_HELPER_MAX_SEND_DELAY))
        if resume_count is None:
            offset, index, sent_count, target_count = self._load_progress("inline", source_bot)
        else:
            offset, index = await self._locate_inline_cursor(source_bot, resume_count)
            sent_count = resume_count
            target_count = resume_count
        self.runner_stop_event = asyncio.Event()
        self.state = AddHelperRunnerState(True, "inline", sent_count, delay_seconds, self.resolved_target_chat, offset, index, "", source_bot, target_count)
        self._save_progress(source_bot, offset, index)
        self.runner_task = asyncio.create_task(self._worker_inline(source_bot))

    async def _worker_inline(self, source_bot: str):
        offset = self.state.current_offset or ""
        start_index = self.state.current_index or 0
        try:
            while not self.runner_stop_event.is_set():
                results = await self._get_inline_results(source_bot, offset)
                if not results.results:
                    if ADD_HELPER_CLEAR_STATE_ON_FINISH:
                        add_helper_clear_progress()
                    break
                safe_start = max(0, min(start_index, len(results.results)))
                for idx in range(safe_start, len(results.results)):
                    if self.runner_stop_event.is_set():
                        break
                    result = results.results[idx]
                    await self._send_inline_result(source_bot, results, result.id)
                    self.state.sent_count += 1
                    self.state.current_offset = offset
                    self.state.current_index = idx + 1
                    self._save_progress(source_bot, offset, idx + 1)
                    logger.info("AddHelper sent #%s inline result from %s", self.state.sent_count, source_bot)
                    await self._sleep_with_stop(self.state.delay_seconds)
                if self.runner_stop_event.is_set():
                    break
                offset = results.next_offset or ""
                start_index = 0
                self.state.current_offset = offset
                self.state.current_index = 0
                self._save_progress(source_bot, offset, 0)
                if not offset:
                    if ADD_HELPER_CLEAR_STATE_ON_FINISH:
                        add_helper_clear_progress()
                    break
        except Exception as e:
            self.state.last_error = str(e)
            logger.exception("AddHelper inline worker failed")
            await self._notify_error("inline", source_bot)
        finally:
            self.state.running = False

    async def _collect_forward_media_ids(self, source_chat: str, media_filter: str = "all") -> list[int]:
        media_filter = (media_filter or "all").lower().strip()
        media_ids: list[int] = []
        async for msg in self.client.get_chat_history(source_chat):
            document = getattr(msg, "document", None)
            has_photo = bool(getattr(msg, "photo", None))
            has_video = bool(
                getattr(msg, "video", None)
                or getattr(msg, "animation", None)
                or (
                    document
                    and str(getattr(document, "mime_type", "") or "").startswith("video/")
                )
            )

            if media_filter == "video":
                if has_video:
                    media_ids.append(int(msg.id))
            elif media_filter == "photo":
                if has_photo:
                    media_ids.append(int(msg.id))
            else:
                if has_photo or has_video:
                    media_ids.append(int(msg.id))

        media_ids.reverse()
        return media_ids

    async def _forward_message(self, source_chat: str, message_id: int):
        from pyrogram.errors import FloodWait, RPCError
        last_exc = None
        for attempt in range(1, ADD_HELPER_MAX_RETRIES + 1):
            if self.runner_stop_event.is_set():
                raise asyncio.CancelledError()
            try:
                await self.client.forward_messages(chat_id=self.resolved_target_chat, from_chat_id=source_chat, message_ids=message_id)
                return
            except FloodWait as e:
                wait_for = int(getattr(e, "value", getattr(e, "x", 5)))
                self.state.last_error = f"FloodWait(forward): {wait_for}s"
                await self._sleep_with_stop(wait_for + 1)
                last_exc = e
            except (RPCError, OSError, TimeoutError, ValueError) as e:
                self.state.last_error = f"forward retry error: {e}"
                last_exc = e
                if attempt < ADD_HELPER_MAX_RETRIES:
                    await self._sleep_with_stop(self._backoff_delay(attempt))
        raise RuntimeError(f"forward_messages failed: {last_exc}")

    async def start_forward(self, source_chat: str, delay_seconds: int, resume_count: Optional[int] = None, media_filter: str = "all"):
        if self.is_running():
            raise RuntimeError("AddHelper is already running")
        delay_seconds = max(1, min(delay_seconds, ADD_HELPER_MAX_SEND_DELAY))
        media_filter = (media_filter or "all").lower().strip()
        media_ids = await self._collect_forward_media_ids(source_chat, media_filter=media_filter)
        if not media_ids:
            raise RuntimeError(f"No {media_filter if media_filter != 'all' else 'photo/video'} posts found in {source_chat}")
        progress_mode = f"forward:{media_filter}" if media_filter != "all" else "forward"
        if resume_count is None:
            _, index, sent_count, target_count = self._load_progress(progress_mode, source_chat)
        else:
            index = resume_count
            sent_count = resume_count
            target_count = resume_count
        if index >= len(media_ids):
            raise RuntimeError(f"Resume index {index} is at/after the end ({len(media_ids)})")
        self.runner_stop_event = asyncio.Event()
        self.state = AddHelperRunnerState(True, f"forward:{media_filter}" if media_filter != "all" else "forward", sent_count, delay_seconds, self.resolved_target_chat, "", index, "", source_chat, target_count)
        self._save_progress(source_chat, "", index)
        self.runner_task = asyncio.create_task(self._worker_forward(source_chat, media_ids))

    async def _worker_forward(self, source_chat: str, media_ids: list[int]):
        try:
            start_index = max(0, min(self.state.current_index or 0, len(media_ids)))
            for idx in range(start_index, len(media_ids)):
                if self.runner_stop_event.is_set():
                    break
                mid = media_ids[idx]
                await self._forward_message(source_chat, mid)
                self.state.sent_count += 1
                self.state.current_index = idx + 1
                self.state.current_offset = str(mid)
                self._save_progress(source_chat, str(mid), idx + 1)
                logger.info("AddHelper forwarded #%s msg_id=%s from %s", self.state.sent_count, mid, source_chat)
                await self._sleep_with_stop(self.state.delay_seconds)
            if not self.runner_stop_event.is_set() and self.state.current_index >= len(media_ids):
                if ADD_HELPER_CLEAR_STATE_ON_FINISH:
                    add_helper_clear_progress()
        except Exception as e:
            self.state.last_error = str(e)
            logger.exception("AddHelper forward worker failed")
            await self._notify_error("forward", source_chat)
        finally:
            self.state.running = False

    async def _notify_error(self, mode: str, source: str) -> None:
        try:
            await self._reply("⚠️ AddHelper Stopped\n\n" f"Mode: {mode}\n" f"Source: {source}\n" f"Sent count: {self.state.sent_count}\n" f"Current offset: {self.state.current_offset or '-'}\n" f"Current index: {self.state.current_index}\n" f"Last error: {self.state.last_error or 'unknown'}")
        except Exception:
            logger.exception("AddHelper failed to notify error")

    def _help_text(self) -> str:
        lines = ["AddHelper ready ✅", "", f"Target chat: {self.resolved_target_chat}", f"Default delay: {ADD_HELPER_DEFAULT_SEND_DELAY}s", "", "Inline commands:"]
        for src in ADD_HELPER_SOURCES:
            lines.append(f"• {src.title}: {src.start_aliases[0]} [delay] | {src.resume_aliases[0]} <count> [delay]")
        lines += ["", "Forward channel commands:"]
        for src in ADD_HELPER_SOURCES:
            if src.forward_chat and src.forward_start_aliases:
                lines.append(f"• {src.title}: {src.forward_start_aliases[0]} [delay] | {src.forward_resume_aliases[0]} <count> [delay]")
        lines += ["", "Forward video-only commands:"]
        for src in ADD_HELPER_SOURCES:
            if src.forward_chat and src.forward_start_aliases:
                video_cmd = src.forward_start_aliases[0].replace("bot", "videobot")
                video_resume = src.forward_resume_aliases[0].replace("bot", "videobot")
                lines.append(f"• {src.title}: {video_cmd} [delay] | {video_resume} <count> [delay]")
        lines += ["", "Other: /helperstatus /stophelper /resethelperprogress"]
        return "\n".join(lines)

    async def _execute_control_command(self, msg) -> None:
        text = add_helper_clean(getattr(msg, "text", "") or "")
        cmd = add_helper_command_name(text)
        if cmd in {"/addhelper", "/helper", "/helperstart", "/starthelper"}:
            await self._reply(self._help_text(), reply_to_message_id=msg.id)
            return
        if cmd in {"/helperstatus", "/addhelperstatus"}:
            s = self.state
            await self._reply(f"Running: {'YES' if self.is_running() else 'NO'}\nMode: {s.runner_mode or '-'}\nSource: {s.source_ref or '-'}\nTarget chat: {s.target_chat}\nDelay: {s.delay_seconds}s\nSent count: {s.sent_count}\nCurrent offset: {s.current_offset or '-'}\nCurrent index: {s.current_index}\nResume target count: {s.resume_target_count}\nLast error: {s.last_error or '-'}", reply_to_message_id=msg.id)
            return
        if cmd in {"/stophelper", "/stopinlinebot"}:
            stopped = await self.stop_runner()
            await self._reply("Stopped." if stopped else "AddHelper is not running.", reply_to_message_id=msg.id)
            return
        if cmd in {"/resethelperprogress", "/resetinlineprogress"}:
            if self.is_running():
                await self._reply("AddHelper running ဖြစ်နေပါတယ်။ အရင် /stophelper လုပ်ပါ။", reply_to_message_id=msg.id)
                return
            add_helper_clear_progress()
            await self._reply("AddHelper progress cleared.", reply_to_message_id=msg.id)
            return
        if cmd in ADD_HELPER_START_COMMANDS:
            src = ADD_HELPER_START_COMMANDS[cmd]
            delay = add_helper_parse_delay(text, ADD_HELPER_DEFAULT_SEND_DELAY)
            await self.start_inline(src.inline_bot, delay)
            await self._reply(f"Started inline.\nSource: {src.inline_bot}\nDelay: {delay}s\nResume offset: {self.state.current_offset or '-'}\nResume index: {self.state.current_index}", reply_to_message_id=msg.id)
            return
        if cmd in ADD_HELPER_RESUME_COMMANDS:
            src = ADD_HELPER_RESUME_COMMANDS[cmd]
            count, delay = add_helper_parse_resume(text, ADD_HELPER_DEFAULT_SEND_DELAY)
            await self.start_inline(src.inline_bot, delay, resume_count=count)
            await self._reply(f"Force resume inline started.\nSource: {src.inline_bot}\nCount: {count}\nDelay: {delay}s\nResolved offset: {self.state.current_offset or '-'}\nResolved index: {self.state.current_index}", reply_to_message_id=msg.id)
            return
        if cmd in ADD_HELPER_FW_START_COMMANDS:
            src = ADD_HELPER_FW_START_COMMANDS[cmd]
            delay = add_helper_parse_delay(text, ADD_HELPER_DEFAULT_SEND_DELAY)
            await self.start_forward(src.forward_chat, delay)
            await self._reply(f"Started forward.\nSource: {src.forward_chat}\nDelay: {delay}s\nResume index: {self.state.current_index}", reply_to_message_id=msg.id)
            return
        if cmd in ADD_HELPER_FW_RESUME_COMMANDS:
            src = ADD_HELPER_FW_RESUME_COMMANDS[cmd]
            count, delay = add_helper_parse_resume(text, ADD_HELPER_DEFAULT_SEND_DELAY)
            await self.start_forward(src.forward_chat, delay, resume_count=count)
            await self._reply(f"Force resume forward started.\nSource: {src.forward_chat}\nCount: {count}\nDelay: {delay}s\nResolved index: {self.state.current_index}", reply_to_message_id=msg.id)
            return
        if cmd in ADD_HELPER_FW_VIDEO_START_COMMANDS:
            src = ADD_HELPER_FW_VIDEO_START_COMMANDS[cmd]
            delay = add_helper_parse_delay(text, ADD_HELPER_DEFAULT_SEND_DELAY)
            await self.start_forward(src.forward_chat, delay, media_filter="video")
            await self._reply(f"Started forward video-only.\nSource: {src.forward_chat}\nDelay: {delay}s\nResume index: {self.state.current_index}", reply_to_message_id=msg.id)
            return
        if cmd in ADD_HELPER_FW_VIDEO_RESUME_COMMANDS:
            src = ADD_HELPER_FW_VIDEO_RESUME_COMMANDS[cmd]
            count, delay = add_helper_parse_resume(text, ADD_HELPER_DEFAULT_SEND_DELAY)
            await self.start_forward(src.forward_chat, delay, resume_count=count, media_filter="video")
            await self._reply(f"Force resume forward video-only started.\nSource: {src.forward_chat}\nCount: {count}\nDelay: {delay}s\nResolved index: {self.state.current_index}", reply_to_message_id=msg.id)
            return

    async def _control_loop(self) -> None:
        known = {"/addhelper", "/helper", "/helperstart", "/starthelper", "/helperstatus", "/addhelperstatus", "/stophelper", "/stopinlinebot", "/resethelperprogress", "/resetinlineprogress", *ADD_HELPER_START_COMMANDS.keys(), *ADD_HELPER_RESUME_COMMANDS.keys(), *ADD_HELPER_FW_START_COMMANDS.keys(), *ADD_HELPER_FW_RESUME_COMMANDS.keys(), *ADD_HELPER_FW_VIDEO_START_COMMANDS.keys(), *ADD_HELPER_FW_VIDEO_RESUME_COMMANDS.keys()}
        while not self.stop_event.is_set():
            try:
                last_seen = add_helper_get_control_last_msg_id()
                messages = []
                async for msg in self.client.get_chat_history(self.resolved_target_chat, limit=ADD_HELPER_CONTROL_HISTORY_LIMIT):
                    messages.append(msg)
                messages.reverse()
                newest = last_seen
                for msg in messages:
                    newest = max(newest, int(msg.id))
                    if msg.id <= last_seen:
                        continue
                    text = add_helper_clean(getattr(msg, "text", "") or "")
                    cmd = add_helper_command_name(text)
                    if not text or cmd not in known:
                        continue
                    if not self._is_owner_or_self(msg):
                        continue
                    try:
                        await self._execute_control_command(msg)
                    except Exception as e:
                        logger.exception("AddHelper control command failed")
                        await self._reply(f"AddHelper error: {e}", reply_to_message_id=msg.id)
                if newest > last_seen:
                    add_helper_set_control_last_msg_id(newest)
            except Exception:
                logger.exception("AddHelper control loop failed")
            try:
                await asyncio.wait_for(self.stop_event.wait(), timeout=ADD_HELPER_CONTROL_POLL_INTERVAL)
            except asyncio.TimeoutError:
                pass


ADD_HELPER = AddHelperService()


async def main() -> None:
    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    dp = Dispatcher()
    dp.include_router(router)
    await on_startup(bot)
    runner = await start_web_app(dp, bot)
    try:
        await ADD_HELPER.start()
        if USE_WEBHOOK:
            await asyncio.Event().wait()
        else:
            await bot.delete_webhook(drop_pending_updates=False)
            await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
    finally:
        try:
            await ADD_HELPER.stop()
        except Exception:
            logger.exception("AddHelper shutdown failed")
        try:
            if USE_WEBHOOK:
                await bot.delete_webhook(drop_pending_updates=False)
        except Exception:
            pass
        try:
            await bot.session.close()
        except Exception:
            pass
        try:
            await runner.cleanup()
        except Exception:
            pass


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logger.info("Bot stopped")
