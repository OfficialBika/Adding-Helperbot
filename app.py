import asyncio
import hashlib
import logging
import os
import re
import shlex
import tempfile
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime, timezone
from io import BytesIO
from pathlib import Path
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
from PIL import Image, ImageOps

load_dotenv()
from helper.controller import HelperController
from helper.commands import COMMANDS, RESUME_PREFIX
from helper.runtime import HelperRuntime

# DM helper controller (isolated crawler flow)
from helper.controller import HelperController
DM_HELPER = HelperController()


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

# Source-specific log/archive channels.
# Sources not listed here continue using ADDED_LOG_CHANNEL.
def parse_chat_ref(value: str):
    value = (value or "").strip()
    if value and value.lstrip("-").isdigit():
        return int(value)
    return value


SOURCE_LOG_CHANNELS = {
    "character_catcher": parse_chat_ref(
        os.getenv("LOG_CHANNEL_CHARACTER_CATCHER", "-1004399932601")
    ),
    "takers_character": parse_chat_ref(
        os.getenv("LOG_CHANNEL_TAKERS_CHARACTER", "-1004497919582")
    ),
    "characters_hallow": parse_chat_ref(
        os.getenv("LOG_CHANNEL_CHARACTERS_HALLOW", "-1003592722414")
    ),
    "waifux_grab": parse_chat_ref(
        os.getenv("LOG_CHANNEL_WAIFUX_GRAB", "-1003914166607")
    ),
    "senpai_catcher": parse_chat_ref(
        os.getenv("LOG_CHANNEL_SENPAI_CATCHER", "-1004453629279")
    ),
}

SENPAI_BOT_ID = int(os.getenv("SENPAI_BOT_ID", "8532697507") or 8532697507)

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

ENABLE_TELEGRAM_RESTART = os.getenv("ENABLE_TELEGRAM_RESTART", "false").lower() == "true"
PM2_PROCESS_NAME = os.getenv("PM2_PROCESS_NAME", "adderbotv2").strip() or "adderbotv2"
PM2_BIN = os.getenv("PM2_BIN", "pm2").strip() or "pm2"


CHECKINLINE_MAX_PAGES = int(os.getenv("CHECKINLINE_MAX_PAGES", "5000"))

# Media fingerprint schema shared with Lookup V3.
MEDIA_SCHEMA_VERSION = 3
MEDIA_FINGERPRINT_VERSION = "media-fp-v3"
PHOTO_HASH_VERSION = "photo-v3.1"
VIDEO_HASH_VERSION = "video-v3.1"

# Keep the old 3-point frame hashes for backward compatibility, while also
# storing a denser V3 fingerprint for more robust video lookup.
VIDEO_LEGACY_SAMPLE_POINTS = (0.20, 0.50, 0.80)
VIDEO_V3_SAMPLE_POINTS = (0.05, 0.15, 0.30, 0.50, 0.70, 0.85, 0.95)

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
items = db.items  # old collection name kept for compatibility
sudo_users = db.sudo_users
known_users = db.known_users
user_modes = db.user_modes
settings_col = db.settings

router = Router()

HELPER_CONTROLLER = HelperController()
HELPER_RUNTIME = HelperRuntime()

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
    forward_chat_ids: tuple[int, ...] = ()
    forward_user_ids: tuple[int, ...] = ()
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
    media_geometry: dict[str, Any] = field(default_factory=dict)
    photo_fingerprint: Optional[dict[str, Any]] = None
    video_fingerprint: Optional[dict[str, Any]] = None
    fingerprint_version: str = MEDIA_FINGERPRINT_VERSION

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
    text = normalize_stylized_latin(text)
    text = text.replace("\r", "\n")
    text = text.replace("：", ":").replace("﹕", ":").replace("꞉", ":")
    text = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", text)
    text = re.sub(r"[ \t]+", " ", text)
    return text.strip()


def strip_leading_symbols(value: str) -> str:
    value = clean_value(value)
    return re.sub(
        r"^[^\w\u00C0-\u024F\u0400-\u04FF\u3040-\u30FF\u4E00-\u9FFF\uAC00-\uD7AF]+",
        "",
        value,
    ).strip()


def strip_grab_name_suffix(value: str) -> str:
    value = clean_value(value)
    return clean_value(re.sub(r"\s*[-–—|]+\s*(?:rarity|anime|id)\b.*$", "", value, flags=re.IGNORECASE))


def clean_rarity_value(value: str) -> str:
    value = clean_value(value)
    value = value.strip("()[]{} ")
    value = strip_leading_symbols(value)
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


# Telegram channel captions sometimes use Unicode small-cap Latin letters
# (example: ɴᴀᴍᴇ, ᴄʜᴀʀ ɪᴅ). NFKC does not convert these characters,
# so we transliterate them before parsing labels and values.
STYLIZED_LATIN_TRANSLATION = str.maketrans({
    "ᴀ": "A", "ʙ": "B", "ᴄ": "C", "ᴅ": "D", "ᴇ": "E",
    "ꜰ": "F", "ɢ": "G", "ʜ": "H", "ɪ": "I", "ᴊ": "J",
    "ᴋ": "K", "ʟ": "L", "ᴍ": "M", "ɴ": "N", "ᴏ": "O",
    "ᴘ": "P", "ʀ": "R", "ꜱ": "S", "ᴛ": "T", "ᴜ": "U",
    "ᴠ": "V", "ᴡ": "W", "ʏ": "Y", "ᴢ": "Z",
    "ᵃ": "A", "ᵇ": "B", "ᶜ": "C", "ᵈ": "D", "ᵉ": "E",
    "ᶠ": "F", "ᵍ": "G", "ʰ": "H", "ᶦ": "I", "ʲ": "J",
    "ᵏ": "K", "ˡ": "L", "ᵐ": "M", "ⁿ": "N", "ᵒ": "O",
    "ᵖ": "P", "ʳ": "R", "ˢ": "S", "ᵗ": "T", "ᵘ": "U",
    "ᵛ": "V", "ʷ": "W", "ˣ": "X", "ʸ": "Y", "ᶻ": "Z",
})


def normalize_stylized_latin(value: str) -> str:
    return (value or "").translate(STYLIZED_LATIN_TRANSLATION)


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

OWO_HEADER_RE = re.compile(r"OwO!\s*Check\s+out\s+(?:this\s+)?(?:character|husbando|waifu)!!?", re.IGNORECASE)
RORONOA_HEADER_RE = re.compile(r"^(?:woah|whoa|wow)!?\s*check\s+out\s+(?:this\s+)?character!?$", re.IGNORECASE)
ID_NAME_COLON_RE = re.compile(r"^\s*(?:ID\s*)?(\d+)\s*[:\-]\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
ID_NAME_SPACE_RE = re.compile(r"^\s*(\d+)\s+(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
ID_NAME_LINE_RE = re.compile(r"^\s*(?:🆔|ID|Id|id)?\s*#?\s*(\d+)\s*[:：]\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)

SMASH_ID_RE = re.compile(r"^[^\n\r]*?(?:\bID\b|🆔)\s*[:\-]?\s*#?\s*([0-9]+)\s*$", re.IGNORECASE | re.MULTILINE)
WAIFUX_NAME_RE = re.compile(r"^[^\n\r]*?➤\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
WAIFUX_SERIES_RE = re.compile(r"^[^\n\r]*?\bSeries\b\s*[:\-]?\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
WAIFUX_ID_RE = re.compile(r"^[^\n\r]*?\bID\b\s*[:\-]?\s*#?\s*([0-9]+)\s*$", re.IGNORECASE | re.MULTILINE)

SENPAI_NAME_RE = re.compile(
    r"^[^\n\r]*?\bName\b\s*[:：\-]\s*(.+?)\s*$",
    re.IGNORECASE | re.MULTILINE,
)
SENPAI_ANIME_RE = re.compile(
    r"^[^\n\r]*?\bAnime\b\s*[:：\-]\s*(.+?)\s*$",
    re.IGNORECASE | re.MULTILINE,
)
SENPAI_RARITY_RE = re.compile(
    r"^[^\n\r]*?\bRarity\b\s*[:：\-]\s*(.+?)\s*$",
    re.IGNORECASE | re.MULTILINE,
)
SENPAI_ID_RE = re.compile(
    r"^[^\n\r]*?(?:🆔\s*)?(?:\bCHAR\s*)?\bID\b\s*[:：\-]?\s*#?\s*([0-9]+)\s*$",
    re.IGNORECASE | re.MULTILINE,
)

# SenpaiCatcher / DB captions may use Unicode small caps and may arrive as
# multiline caption, flattened one-line text, or nested inside Bot API dump.
SENPAI_DB_HINT_RE = re.compile(
    r"new\s+character\s+added\s+to\s+the\s+bot|char\s*id\s*[:：\-]|\bname\b\s*[:：\-].*\banime\b\s*[:：\-].*\brarity\b\s*[:：\-]",
    re.IGNORECASE | re.DOTALL,
)
SENPAI_NEXT_LABEL = r"(?:🆔\s*)?(?:CHAR\s*)?ID|(?:👤\s*)?NAME|(?:📺\s*)?ANIME|(?:💎\s*)?RARITY|(?:➕\s*)?ADDED\s+BY|NEW\s+CHARACTER"


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
    SourceDef(
        "waifux_grab",
        "items_waifux_grab",
        "/grab",
        "@WaifuxGrabBot",
        ("WaifuxGrabBot", "waifuxgrabbot"),
        forward_usernames=("WAIFUXGRAB_DATABASE", "waifuxgrab_database"),
        forward_titles=(
            "WAIFUXGRAB",
            "WAIFUXGRAB DATABASE",
            "WAIFUXGRAB_DATABASE",
            "WaifuxGrab Database",
        ),
        parser="waifux",
        save_rarity=True,
    ),
    SourceDef("catch_your_waifu", "items_catch_your_waifu", "/guess", "@Catch_Your_Waifu_Bot", ("Catch_Your_Waifu_Bot", "catch_your_waifu_bot"), parser="owo_colon"),
    SourceDef("waifu_grabber", "items_waifu_grabber", "/grab", "@Waifu_Grabber_Bot", ("Waifu_Grabber_Bot", "waifu_grabber_bot"), parser="owo_colon"),
    # New inline sources requested by owner
    SourceDef("roronoa_zoro", "items_roronoa_zoro", "/challenge", "@roronoa_zoro_robot", ("roronoa_zoro_robot",), parser="name_only", save_rarity=False),
    SourceDef("character_picker", "items_character_picker", "/pick", "@character_picker_bot", ("character_picker_bot",), parser="owo_colon"),
    SourceDef(
        "senpai_catcher",
        "items_senpai_catcher",
        "/pick",
        "@SenpaiCatcherBot",
        ("SenpaiCatcherBot", "senpaicatcherbot"),
        forward_usernames=(
            "SenpaiCatcherBot",
            "senpaicatcherbot",
            "fafafawfawfa",
        ),
        forward_titles=(
            "SenpaiCatcher",
            "SenpaiCatcher🎞.",
            "SenpaiCatcher.",
            "SenpaiCatcher / DB",
            "🦠 SenpaiCatcher / DB",
            "SenpaiCatcher DB",
            "senpai database",
        ),
        forward_user_ids=(SENPAI_BOT_ID,),
        parser="senpai",
    ),
    SourceDef(
        "bika_character",
        "items_bika_character",
        "/bika",
        "@BikaCharacterBot",
        ("BikaCharacterBot", "bikacharacterbot"),
        forward_titles=("Bika Waifu Database",),
        forward_chat_ids=(-1003923540741,),
        parser="label",
    ),
    SourceDef(
        "orinx_waifu",
        "items_orinx_waifu",
        "/orin",
        "@orinx_catcher_waifu_bot",
        ("orinx_catcher_waifu_bot", "Orinx_Catcher_Waifu_Bot"),
        forward_usernames=("timunagalaya",),
        forward_titles=(
            "-1003598338404",
            "OrinX Waifu Bot",
            "OrinX Waifu",
            "OrinX Waifu Database",
            "CHARACTER DATABASE",
        ),
        forward_chat_ids=(-1003598338404,),
        parser="label",
        save_rarity=True,
    ),
    SourceDef(
        "immortal_donghua",
        "items_immortal_donghua",
        "/dao",
        "@ImmortalDonghuaBot",
        ("ImmortalDonghuaBot", "immortaldonghuabot"),
        forward_titles=(
            "𝗗𝗼𝗻𝗴𝗵𝘂𝗮 Database 𝗖𝗵𝗮𝗻𝗻𝗲𝗹",
            "Donghua Database Channel",
            "Donghua Database",
        ),
        forward_chat_ids=(-1004397263975,),
        parser="label",
        save_rarity=True,
    ),
    SourceDef(
        "super_zeko",
        "items_super_zeko",
        "/ziceko",
        "@Super_zeko_bot",
        ("Super_zeko_bot", "super_zeko_bot"),
        forward_usernames=("zicekodata_1",),
        forward_titles=("Myanmar Character Logs", "Myanmar Character", "Myanmar Character Log"),
        parser="myanmar_character",
    ),
]

SOURCE_BY_KEY = {src.key: src for src in SOURCE_CONFIGS}
SOURCE_BY_INLINE_USERNAME: dict[str, SourceDef] = {}
SOURCE_BY_FORWARD_USERNAME: dict[str, SourceDef] = {}
SOURCE_BY_FORWARD_TITLE: dict[str, SourceDef] = {}
SOURCE_BY_FORWARD_CHAT_ID: dict[int, SourceDef] = {}
SOURCE_BY_FORWARD_USER_ID: dict[int, SourceDef] = {}

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
    for chat_id in src.forward_chat_ids:
        if chat_id:
            SOURCE_BY_FORWARD_CHAT_ID[int(chat_id)] = src
    for user_id in src.forward_user_ids:
        if user_id:
            SOURCE_BY_FORWARD_USER_ID[int(user_id)] = src


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


def resolve_source_from_arg(raw_arg: Optional[str]) -> Optional[SourceDef]:
    arg = clean_value(raw_arg or "")
    if not arg:
        return None
    first = arg.split()[0]
    key = first.strip().lstrip("@").casefold().replace("-", "_")
    if key in SOURCE_BY_KEY:
        return SOURCE_BY_KEY[key]
    inline_key = norm_username(first)
    if inline_key in SOURCE_BY_INLINE_USERNAME:
        return SOURCE_BY_INLINE_USERNAME[inline_key]
    cmd = clean_command_name(first) if first.startswith("/") else ""
    if cmd:
        for src in SOURCE_CONFIGS:
            if src.command == cmd:
                return src
    for src in SOURCE_CONFIGS:
        if key == norm_username(src.bot_username):
            return src
    return None


# -----------------------------------------------------
# Telegram source helpers
# -----------------------------------------------------
def collect_candidate_texts(message: Message) -> list[str]:
    candidates: list[str] = []

    def add_candidate(value: Any, *, require_hint: bool = False) -> None:
        if value is None or not isinstance(value, str):
            return
        value = normalize_parse_text(value)
        if not value:
            return
        if require_hint and not SENPAI_DB_HINT_RE.search(value):
            return
        if value not in candidates:
            candidates.append(value)

    # Normal Bot API fields.
    for value in [
        getattr(message, "caption", None),
        getattr(message, "text", None),
        getattr(message, "html_text", None),
        getattr(message, "md_text", None),
    ]:
        add_candidate(value)

    # Extra/reply fields can contain the forwarded post caption on some clients.
    for obj in [
        getattr(message, "external_reply", None),
        getattr(message, "reply_to_message", None),
    ]:
        if obj is None:
            continue
        for value in [
            getattr(obj, "caption", None),
            getattr(obj, "text", None),
            getattr(obj, "html_text", None),
            getattr(obj, "md_text", None),
        ]:
            add_candidate(value)

    # Last-resort scan: forwarded captions can be nested inside model_dump().
    # Keep only strings that look like a Senpai DB caption.
    try:
        dumped = message.model_dump()
    except Exception:
        dumped = None

    def walk(obj: Any) -> None:
        if obj is None:
            return
        if isinstance(obj, str):
            add_candidate(obj, require_hint=True)
            return
        if isinstance(obj, dict):
            for value in obj.values():
                walk(value)
            return
        if isinstance(obj, (list, tuple)):
            for value in obj:
                walk(value)

    walk(dumped)
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


def get_sender_source_def(message: Message) -> Optional[SourceDef]:
    user = getattr(message, "from_user", None)
    if user is None:
        return None
    username = norm_username(getattr(user, "username", "") or "")
    if not username:
        return None
    return SOURCE_BY_INLINE_USERNAME.get(username)


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
    info: dict[str, Any] = {
        "chat_id": None,
        "message_id": None,
        "user_id": None,
        "username": "",
        "title": "",
        "origin_type": "",
    }

    origin = getattr(message, "forward_origin", None)
    if origin:
        info["origin_type"] = origin.__class__.__name__
        info["message_id"] = getattr(origin, "message_id", None)

        chat = getattr(origin, "chat", None) or getattr(origin, "sender_chat", None)
        if chat is not None:
            info["chat_id"] = getattr(chat, "id", None)
            info["username"] = norm_username(getattr(chat, "username", "") or "")
            info["title"] = normalize_forward_mapping_key(getattr(chat, "title", "") or "")
            return info

        sender_user = getattr(origin, "sender_user", None)
        if sender_user is not None:
            info["user_id"] = getattr(sender_user, "id", None)
            info["username"] = norm_username(getattr(sender_user, "username", "") or "")
            info["title"] = normalize_forward_mapping_key(
                getattr(sender_user, "full_name", "")
                or getattr(sender_user, "first_name", "")
                or ""
            )
            return info

        sender_user_name = clean_value(getattr(origin, "sender_user_name", "") or "")
        if sender_user_name:
            info["title"] = normalize_forward_mapping_key(sender_user_name)
            info["username"] = norm_username(sender_user_name)
            return info

    legacy_chat = getattr(message, "forward_from_chat", None)
    if legacy_chat is not None:
        info["chat_id"] = getattr(legacy_chat, "id", None)
        info["message_id"] = getattr(message, "forward_from_message_id", None)
        info["username"] = norm_username(getattr(legacy_chat, "username", "") or "")
        info["title"] = normalize_forward_mapping_key(getattr(legacy_chat, "title", "") or "")
        info["origin_type"] = "legacy_forward_chat"
        return info

    legacy_user = getattr(message, "forward_from", None)
    if legacy_user is not None:
        info["user_id"] = getattr(legacy_user, "id", None)
        info["username"] = norm_username(getattr(legacy_user, "username", "") or "")
        info["title"] = normalize_forward_mapping_key(
            getattr(legacy_user, "full_name", "")
            or getattr(legacy_user, "first_name", "")
            or ""
        )
        info["origin_type"] = "legacy_forward_user"
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
    chat_id = info.get("chat_id")
    user_id = info.get("user_id")
    try:
        chat_id_int = int(chat_id) if chat_id is not None else None
    except Exception:
        chat_id_int = None
    try:
        user_id_int = int(user_id) if user_id is not None else None
    except Exception:
        user_id_int = None

    if user_id_int is not None and user_id_int in SOURCE_BY_FORWARD_USER_ID:
        return SOURCE_BY_FORWARD_USER_ID[user_id_int]

    # Strong Senpai DB source fallback. Telegram may show the channel as
    # "🦠 SenpaiCatcher / DB" while usernames/titles vary by forward type.
    senpai_src = SOURCE_BY_KEY.get("senpai_catcher")
    if senpai_src:
        if user_id_int == SENPAI_BOT_ID:
            return senpai_src
        if username in {"senpaicatcherbot", "fafafawfawfa"}:
            return senpai_src
        if "senpaicatcher" in title or "senpai database" in title:
            return senpai_src

    if chat_id_int is not None and chat_id_int in SOURCE_BY_FORWARD_CHAT_ID:
        return SOURCE_BY_FORWARD_CHAT_ID[chat_id_int]
    if username and username in SOURCE_BY_FORWARD_USERNAME:
        return SOURCE_BY_FORWARD_USERNAME[username]
    if title and title in SOURCE_BY_FORWARD_TITLE:
        return SOURCE_BY_FORWARD_TITLE[title]
    for key, src in SOURCE_BY_FORWARD_TITLE.items():
        if key and title and (key in title or title in key):
            return src

    # If forward title is hidden but caption is clearly Senpai DB format, still save
    # to the Senpai collection instead of treating it as unsupported.
    raw = get_combined_message_text(message)
    if senpai_src and SENPAI_DB_HINT_RE.search(raw or ""):
        return senpai_src
    return None


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
    sender_src = get_sender_source_def(message)
    if sender_src:
        return f"sender {sender_src.bot_username}"
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



def parse_name_only_message(message: Message, src: SourceDef) -> ParsedText:
    raw = get_combined_message_text(message)
    lines = lines_from_text(raw)
    name: Optional[str] = None
    for line in lines:
        cleaned = clean_value(line)
        if not cleaned:
            continue
        if RORONOA_HEADER_RE.search(cleaned):
            continue
        if OWO_HEADER_RE.search(cleaned):
            continue
        if re.search(r"\b(?:defeat\s+count|rarity|event|id)\b", cleaned, re.IGNORECASE):
            continue
        name = strip_leading_symbols(cleaned)
        break
    return finalize_parsed_text(
        ParsedText(name=name, anime_name=None, rarity=None, card_id=None, command_name=src.command, raw_text=raw, source_key=src.key)
    )


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
        if match and len(match.groups()) >= 2:
            card_id = clean_value(match.group(1))
            name = clean_value(match.group(2))
            match_line = clean_value(match.group(0))
            break
    if match_line in lines:
        anime_name = infer_anime_from_lines(lines, lines.index(match_line))
    else:
        for line in lines:
            if OWO_HEADER_RE.search(line) or RORONOA_HEADER_RE.search(line):
                continue
            if card_id and line.startswith(card_id):
                break
            if re.search(r"\b(?:rarity|event|globally\s+catches|added\s*by)\b", line, re.IGNORECASE):
                continue
            anime_name = strip_leading_symbols(line)
            break

    return finalize_parsed_text(
        ParsedText(
            name=name,
            anime_name=anime_name,
            rarity=parse_field(raw, RARITY_PATTERNS) if src.save_rarity else None,
            card_id=card_id,
            command_name=src.command,
            raw_text=raw,
            source_key=src.key,
        )
    )


def parse_capture_or_seizer_message(message: Message, src: SourceDef) -> ParsedText:
    label = parse_label_message(message, src)
    if label.name and label.card_id:
        return label
    owo = parse_owo_message(message, src, mode="colon")
    if owo.name and owo.card_id:
        return owo
    return label


SMASH_LOOK_LINE_RE = re.compile(r"look\s+at\s+this\s+character\s*(?:\n|\s)+(.+?)\s+from\s+(.+?)(?:!|！|\n|$)", re.IGNORECASE | re.DOTALL)
SMASH_FROM_LINE_RE = re.compile(r"^(.+?)\s+from\s+(.+?)(?:!|！)?$", re.IGNORECASE)
SMASH_ANIME_COUNT_RE = re.compile(r"\s+\d+\s*/\s*\d+\s*$")


def clean_smash_text_value(value: str) -> str:
    value = strip_leading_symbols(value)
    value = value.strip(" !！.,;:()[]{}")
    return clean_value(value)


def clean_smash_anime_value(value: str) -> str:
    value = clean_smash_text_value(value)
    value = SMASH_ANIME_COUNT_RE.sub("", value).strip()
    return clean_value(value)


def parse_smash_message(message: Message, src: SourceDef) -> ParsedText:
    raw = get_combined_message_text(message)
    lines = lines_from_text(raw)
    name: Optional[str] = None
    anime_name: Optional[str] = None

    look_match = SMASH_LOOK_LINE_RE.search(raw)
    if look_match:
        name = clean_smash_text_value(look_match.group(1))
        anime_name = clean_smash_anime_value(look_match.group(2))

    if not name or not anime_name:
        for line in lines:
            match = SMASH_FROM_LINE_RE.match(clean_smash_text_value(line))
            if match:
                name = name or clean_smash_text_value(match.group(1))
                anime_name = anime_name or clean_smash_anime_value(match.group(2))
                break

    if not name or not anime_name:
        useful: list[str] = []
        for line in lines:
            cleaned = clean_smash_text_value(line)
            if not cleaned:
                continue
            if re.search(r"look\s+at\s+this\s+character", cleaned, re.IGNORECASE):
                continue
            if re.search(r"\b(?:rarity|global\s+owners|owners)\b", cleaned, re.IGNORECASE):
                continue
            if re.search(r"(?:\bID\b|🆔)", cleaned, re.IGNORECASE):
                continue
            if SMASH_ANIME_COUNT_RE.search(cleaned):
                anime_candidate = clean_smash_anime_value(cleaned)
                if anime_candidate and not anime_name:
                    anime_name = anime_candidate
                continue
            useful.append(cleaned)
        if not name and useful:
            name = useful[0]
        if not anime_name and len(useful) >= 2:
            anime_name = clean_smash_anime_value(useful[1])

    return finalize_parsed_text(
        ParsedText(name=name, anime_name=anime_name, rarity=parse_field(raw, RARITY_PATTERNS), card_id=parse_field(raw, [SMASH_ID_RE]), command_name=src.command, raw_text=raw, source_key=src.key)
    )


def clean_waifux_name_value(value: Optional[str]) -> Optional[str]:
    value = clean_value(value or "")
    if not value:
        return None
    # WaifuxGrabBot တစ်ခုတည်းအတွက် event/emoji marker မသိမ်းရန်
    value = re.sub(r"[\U0001F1E6-\U0001F1FF\U0001F300-\U0001FAFF\u2600-\u27BF]+", "", value)
    value = re.sub(r"\s*\[\s*\]\s*", " ", value)
    value = re.sub(r"\s*\(\s*\)\s*", " ", value)
    return clean_value(value) or None


def parse_waifux_message(message: Message, src: SourceDef) -> ParsedText:
    raw = get_combined_message_text(message)

    # WAIFUXGRAB_DATABASE forwarded captions use label format:
    # NEW WAIFU ADDED
    # ⋆ Item ID : 2263
    # ⋆ Name : Isabel
    # ⋆ Rarity : Classy 👠
    # ⋆ Category : Legendary 🔵
    # ⋆ Media : Photo
    # This label parser keeps name/card_id/rarity while still forcing
    # source_key=waifux_grab, collection=items_waifux_grab and command=/grab.
    label = parse_label_message(message, src)
    if label.name or label.card_id:
        label.command_name = src.command
        label.source_key = src.key
        return finalize_parsed_text(label)

    # Backward compatibility for older Waifux inline/caption style.
    return finalize_parsed_text(
        ParsedText(
            name=clean_waifux_name_value(parse_field(raw, [WAIFUX_NAME_RE])),
            anime_name=parse_field(raw, [WAIFUX_SERIES_RE]),
            rarity=parse_field(raw, RARITY_PATTERNS) if src.save_rarity else None,
            card_id=parse_field(raw, [WAIFUX_ID_RE]),
            command_name=src.command,
            raw_text=raw,
            source_key=src.key,
        )
    )


def normalize_senpai_text_value(value: Optional[str]) -> Optional[str]:
    value = clean_value(normalize_stylized_latin(unicodedata.normalize("NFKC", value or "")))
    value = re.sub(r"^(?:👤|📺|💎|🆔|➕)+\s*", "", value).strip()
    value = re.sub(r"\s*(?:➕\s*)?ADDED\s+BY\s*[:：\-].*$", "", value, flags=re.IGNORECASE).strip()
    value = clean_value(value)
    # Senpai DB captions are stylized uppercase. Store normalized ASCII uppercase
    # so lookup/result display stays consistent: THORFINN / VINLAND SAGA / JESUS.
    if value and re.search(r"[A-Za-z]", value):
        value = value.upper()
    return value or None


def _senpai_extract_value(raw: str, label_regex: str) -> Optional[str]:
    """Extract a Senpai label value from multiline or flattened caption text."""
    raw = normalize_parse_text(raw)
    if not raw:
        return None
    pattern = re.compile(
        rf"(?:^|[\s\n\r])(?:[^\w\n\r:：\-]{{0,8}}\s*)?(?:{label_regex})\s*[:：\-]\s*(.+?)(?=(?:[\s\n\r]+(?:[^\w\n\r:：\-]{{0,8}}\s*)?(?:{SENPAI_NEXT_LABEL})\s*[:：\-]?)|$)",
        re.IGNORECASE | re.DOTALL,
    )
    match = pattern.search(raw)
    if not match:
        return None
    value = match.group(1)
    value = re.split(r"(?:➕\s*)?ADDED\s+BY\s*[:：\-]", value, maxsplit=1, flags=re.IGNORECASE)[0]
    value = re.sub(r"\s*[-━─➖]{3,}\s*", " ", value)
    return normalize_senpai_text_value(value)


def _senpai_split_line_value(line: str, label_regex: str) -> Optional[str]:
    match = re.search(rf"(?:[^\w\n\r:：\-]{{0,8}}\s*)?(?:{label_regex})\s*[:：\-]\s*(.+)$", line, re.IGNORECASE)
    if not match:
        return None
    return normalize_senpai_text_value(match.group(1))


def parse_senpai_raw_text(raw: str, src: Optional[SourceDef] = None) -> ParsedText:
    src = src or SOURCE_BY_KEY["senpai_catcher"]
    raw = normalize_parse_text(raw)

    card_id: Optional[str] = None
    id_value = _senpai_extract_value(raw, r"(?:CHAR\s*)?ID")
    if id_value:
        id_match = re.search(r"\d+", id_value)
        if id_match:
            card_id = id_match.group(0)

    name = _senpai_extract_value(raw, r"NAME")
    anime_name = _senpai_extract_value(raw, r"ANIME")
    rarity = _senpai_extract_value(raw, r"RARITY")

    # Line-by-line fallback for exact channel captions.
    for line in lines_from_text(raw):
        if not card_id and re.search(r"(?:CHAR\s*)?ID\s*[:：\-]", line, re.IGNORECASE):
            match = re.search(r"\d+", line)
            if match:
                card_id = match.group(0)
        if not name:
            name = _senpai_split_line_value(line, r"NAME")
        if not anime_name:
            anime_name = _senpai_split_line_value(line, r"ANIME")
        if not rarity:
            rarity = _senpai_split_line_value(line, r"RARITY")

    return finalize_parsed_text(
        ParsedText(
            name=name,
            anime_name=anime_name,
            rarity=rarity,
            card_id=card_id,
            command_name=src.command,
            raw_text=raw,
            source_key=src.key,
        )
    )


def parse_senpai_message(message: Message, src: SourceDef) -> ParsedText:
    raw = get_combined_message_text(message)
    parsed = parse_senpai_raw_text(raw, src)
    if not parsed.name:
        info = get_forward_source_info(message)
        logger.warning(
            "Senpai parse failed | forward_info=%s | raw_len=%s | raw_preview=%s",
            info,
            len(raw or ""),
            (raw or "")[:700],
        )
    return parsed


MYANMAR_CHARACTER_HINT_RE = re.compile(
    r"(?:added\s+new\s+character|artwork\s+updated|rarity\s+updated|role\s+updated|character\s+updated|တင်ပြီးပြီ|uploaded\s*\(/?li\)|\buploaded\b|\bmovie\b|\bname\b|\brarity\b|🆔|📛|⭐)",
    re.IGNORECASE,
)
MYANMAR_CHARACTER_HEADERS_RE = re.compile(
    r"(?:added\s+new\s+character|artwork\s+updated|rarity\s+updated|role\s+updated|character\s+updated|တင်ပြီးပြီ|uploaded\s*\(/?li\)|\buploaded\b)",
    re.IGNORECASE,
)
MYANMAR_SEPARATOR_LINE_RE = re.compile(r"^[\s╔╗╚╝═─━┄┅┈┉\-_|╭╮╰╯┌┐└┘]+$")
MYANMAR_NOTICE_RE = re.compile(
    r"(?:သတိပြု|အလိုအလျောက်|drop\s+ကျ|mission\s+လုပ်|leave\s+a\s+comment|comments?\b)",
    re.IGNORECASE,
)
MYANMAR_FIELD_SKIP_RE = re.compile(
    r"\b(?:anime|movie|role|rarity|id|uploaded\s+by|uploader)\b|photo\s+updated|leave\s+a\s+comment|comments?\b",
    re.IGNORECASE,
)


def clean_myanmar_character_field(value: Optional[str], *, keep_symbols: bool = True) -> Optional[str]:
    value = clean_value(normalize_stylized_latin(unicodedata.normalize("NFKC", value or "")))
    if not value:
        return None
    value = value.replace("•", " • ")
    value = clean_value(value)
    if not keep_symbols:
        value = strip_leading_symbols(value)
    return clean_value(value) or None


def clean_myanmar_name_value(value: Optional[str]) -> Optional[str]:
    value = clean_myanmar_character_field(value, keep_symbols=True)
    if not value:
        return None
    # Supports:
    #   📛 Name: Gojo
    #   📛 Suguru Geto
    #   𝗡𝗶𝗹𝗼𝘂 [☃]
    value = re.sub(r"^\s*📛\s*", "", value).strip()
    value = re.sub(r"^\s*(?:Name|NAME)\s*[:：•\-]\s*", "", value, flags=re.IGNORECASE).strip()
    value = re.sub(r"\s*(?:\||•)\s*(?:anime|movie|rarity|role|id)\b.*$", "", value, flags=re.IGNORECASE).strip()
    return clean_value(value) or None


def clean_myanmar_rarity_value(value: Optional[str]) -> Optional[str]:
    value = clean_myanmar_character_field(value, keep_symbols=True)
    if not value:
        return None
    # Supports:
    #   💠 Rarity • 💮 Common 💮
    #   ⭐ Rarity: 💎 Celestial
    #   ⭐ 🧬 Infinity
    value = re.sub(r"^\s*[⭐💠]+\s*", "", value).strip()
    value = re.sub(r"^\s*(?:Rarity|RARITY)\s*[:：•\-]?\s*", "", value, flags=re.IGNORECASE).strip()
    value = re.sub(r"\s*(?:🎭|Role\b).*$", "", value, flags=re.IGNORECASE).strip()
    return clean_value(value) or None


def parse_myanmar_line_field(raw: str, label_regex: str, *, keep_symbols: bool = True) -> Optional[str]:
    # Line-by-line parser for captions with preserved newlines.
    # Allows emoji before label and separators ':', '•', '-'.
    pattern = re.compile(
        rf"^[^\n\r]*?(?:{label_regex})\s*(?:[:：•\-])\s*(.+?)\s*$",
        re.IGNORECASE | re.MULTILINE,
    )
    match = pattern.search(raw or "")
    if not match:
        return None
    value = match.group(1)
    return clean_myanmar_character_field(value, keep_symbols=keep_symbols)


def parse_myanmar_inline_field(raw: str, label_regex: str, *, keep_symbols: bool = True) -> Optional[str]:
    # Fallback for rare flattened captions where labels are in one long line.
    next_label = r"(?:🆔\s*)?ID|(?:📛\s*)?NAME|(?:🎬\s*)?(?:ANIME|MOVIE)|(?:💠|⭐)?\s*RARITY|(?:🎭\s*)?ROLE|(?:👤|📤)\s*(?:UPLOADED\s+BY|UPLOADER)|PHOTO\s+UPDATED|ARTWORK\s+UPDATED"
    pattern = re.compile(
        rf"(?:^|[\s\n\r])[^\w\n\r:：•\-]{{0,8}}(?:{label_regex})\s*(?:[:：•\-])\s*(.+?)(?=(?:\s+[^\w\n\r:：•\-]{{0,8}}(?:{next_label})\s*(?:[:：•\-])?)|$)",
        re.IGNORECASE | re.DOTALL,
    )
    match = pattern.search(raw or "")
    if not match:
        return None
    value = match.group(1)
    return clean_myanmar_character_field(value, keep_symbols=keep_symbols)


def parse_myanmar_field(raw: str, label_regex: str, *, keep_symbols: bool = True) -> Optional[str]:
    return parse_myanmar_line_field(raw, label_regex, keep_symbols=keep_symbols) or parse_myanmar_inline_field(raw, label_regex, keep_symbols=keep_symbols)


def extract_myanmar_character_id(raw: str) -> Optional[str]:
    # Supports both:
    #   🆔 ID: 20
    #   🆔 ID         • 1469
    value = parse_myanmar_field(raw, r"(?:🆔\s*)?ID", keep_symbols=False)
    if value:
        match = re.search(r"\d+", value)
        if match:
            return match.group(0)
    # fallback: line begins with ID emoji and number directly
    match = re.search(r"(?:^|\n)\s*🆔[^\n\r]*?#?\s*(\d+)\b", raw or "", flags=re.IGNORECASE)
    return match.group(1) if match else None


def extract_myanmar_character_rarity(raw: str) -> Optional[str]:
    value = parse_myanmar_field(raw, r"(?:💠\s*)?Rarity", keep_symbols=True)
    if value:
        return clean_myanmar_rarity_value(value)

    # Box format:
    #   ⭐ 🧬 Infinity
    #   🎭 🎴 Normal
    for line in lines_from_text(raw):
        cleaned = clean_myanmar_character_field(line, keep_symbols=True) or ""
        if not cleaned:
            continue
        if re.search(r"\b(?:anime|movie|name|id|role|uploaded|uploader)\b", cleaned, re.IGNORECASE):
            continue
        if cleaned.strip().startswith("⭐"):
            rarity = clean_myanmar_rarity_value(cleaned)
            if rarity:
                return rarity
    return None


def extract_myanmar_character_anime(raw: str) -> Optional[str]:
    value = parse_myanmar_field(raw, r"(?:🎬\s*)?(?:Anime|Movie)", keep_symbols=False)
    if value:
        return strip_leading_symbols(value) or value

    # Box format: anime is usually the line starting with 🎬 without a label.
    for line in lines_from_text(raw):
        cleaned = clean_myanmar_character_field(line, keep_symbols=True) or ""
        if cleaned.strip().startswith("🎬"):
            value = re.sub(r"^\s*🎬\s*", "", cleaned).strip()
            value = re.sub(r"^\s*(?:Anime|Movie)\s*[:：•\-]?\s*", "", value, flags=re.IGNORECASE).strip()
            return strip_leading_symbols(value) or value
    return None


def is_myanmar_noise_line(line: str) -> bool:
    cleaned = clean_myanmar_character_field(line, keep_symbols=True) or ""
    if not cleaned:
        return True
    if MYANMAR_SEPARATOR_LINE_RE.match(cleaned):
        return True
    if MYANMAR_CHARACTER_HEADERS_RE.search(cleaned):
        return True
    if MYANMAR_NOTICE_RE.search(cleaned):
        return True
    if MYANMAR_FIELD_SKIP_RE.search(cleaned):
        return True
    if cleaned.startswith(("✅", "⚠️", "╔", "╚", "║")):
        return True
    return False


def extract_myanmar_character_name(raw: str) -> Optional[str]:
    # Priority 1: explicit label.
    value = parse_myanmar_field(raw, r"(?:📛\s*)?Name", keep_symbols=True)
    name = clean_myanmar_name_value(value)
    if name:
        return name

    lines = lines_from_text(raw)

    # Priority 2: icon-only name line used by Uploaded (/li) format.
    for line in lines:
        cleaned = clean_myanmar_character_field(line, keep_symbols=True) or ""
        if cleaned.strip().startswith("📛") and not re.search(r"\bname\b\s*[:：•\-]", cleaned, re.IGNORECASE):
            name = clean_myanmar_name_value(cleaned)
            if name:
                return name

    # Priority 3: line immediately after a source header, used by Added New Character / Artwork Updated.
    seen_header = False
    fallback: Optional[str] = None
    for line in lines:
        cleaned = clean_myanmar_character_field(line, keep_symbols=True) or ""
        if not cleaned:
            continue
        if MYANMAR_CHARACTER_HEADERS_RE.search(cleaned):
            seen_header = True
            continue
        if is_myanmar_noise_line(cleaned):
            continue
        candidate = clean_myanmar_name_value(cleaned)
        if not candidate:
            continue
        if seen_header:
            return candidate
        if fallback is None:
            fallback = candidate

    return fallback


def looks_like_myanmar_character_source(message: Message) -> bool:
    raw = get_combined_message_text(message)
    if not raw:
        return False
    raw = normalize_parse_text(raw)
    return bool(
        SOURCE_BY_KEY.get("super_zeko")
        and MYANMAR_CHARACTER_HINT_RE.search(raw)
        and (
            extract_myanmar_character_id(raw)
            or extract_myanmar_character_name(raw)
        )
    )


def parse_myanmar_character_message(message: Message, src: SourceDef) -> ParsedText:
    raw = get_combined_message_text(message)
    raw = normalize_parse_text(raw)

    name = extract_myanmar_character_name(raw)
    anime_name = extract_myanmar_character_anime(raw)
    rarity = extract_myanmar_character_rarity(raw) if src.save_rarity else None
    card_id = extract_myanmar_character_id(raw)

    parsed = ParsedText(
        name=clean_myanmar_name_value(name),
        anime_name=clean_myanmar_character_field(anime_name, keep_symbols=False),
        rarity=clean_myanmar_rarity_value(rarity) if rarity else None,
        card_id=clean_value(card_id or "") or None,
        command_name=src.command,
        raw_text=raw,
        source_key=src.key,
    )
    parsed.command_name = clean_command_name(parsed.command_name or src.command)
    return parsed

def parse_caption_text(text: Optional[str]) -> ParsedText:
    raw = normalize_parse_text(text)
    return finalize_parsed_text(
        ParsedText(name=parse_field(raw, NAME_PATTERNS), anime_name=parse_field(raw, ANIME_PATTERNS), rarity=parse_field(raw, RARITY_PATTERNS), card_id=parse_field(raw, CARD_ID_PATTERNS), command_name=parse_command_name(raw), raw_text=raw, source_key=None)
    )


def parse_caption_text_from_message(message: Message) -> ParsedText:
    candidates = collect_candidate_texts(message)
    for raw in candidates:
        parsed = parse_caption_text(raw)
        if parsed.name:
            return parsed
    return parse_caption_text(candidates[0] if candidates else "")


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


def parse_external_source_parser(text: str, src: SourceDef) -> Optional[ParsedText]:
    """Use isolated parsers package for migrated source bots.
    Keeps existing ParsedText/media/database pipeline unchanged.
    """
    try:
        from parsers import character_catcher, senpai as senpai_parser, hallow as hallow_parser, takers as takers_parser, grab as grab_parser
    except Exception:
        return None

    parser_map = {
        "character_catcher": character_catcher.parse,
        "senpai_catcher": senpai_parser.parse,
        "characters_hallow": hallow_parser.parse,
        "takers_character": takers_parser.parse,
        "waifux_grab": grab_parser.parse,
    }

    fn = parser_map.get(src.key)
    if not fn:
        return None

    result = fn(text)
    if not result:
        return None

    return finalize_parsed_text(ParsedText(
        name=result.name,
        anime_name=None,
        rarity=result.rarity,
        card_id=str(result.id) if result.id is not None else None,
        command_name=src.command,
        raw_text=result.raw or text,
        source_key=src.key,
    ))


def get_effective_parsed_message(message: Message) -> ParsedText:
    src = get_inline_source_def(message) or get_forward_source_def(message) or get_sender_source_def(message)
    if src:
        raw_for_external = get_combined_message_text(message)
        external = parse_external_source_parser(raw_for_external, src)
        if external and external.name:
            return external
        if src.parser == "name_only":
            return parse_name_only_message(message, src)
        if src.parser == "smash":
            return parse_smash_message(message, src)
        if src.parser == "waifux":
            return parse_waifux_message(message, src)
        if src.parser == "senpai":
            return parse_senpai_message(message, src)
        if src.parser == "myanmar_character":
            return parse_myanmar_character_message(message, src)
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

    raw = get_combined_message_text(message)
    if SENPAI_DB_HINT_RE.search(raw or ""):
        parsed = parse_senpai_raw_text(raw, SOURCE_BY_KEY["senpai_catcher"])
        if parsed.name:
            return parsed

    super_zeko_src = SOURCE_BY_KEY.get("super_zeko")
    if super_zeko_src and MYANMAR_CHARACTER_HINT_RE.search(raw or ""):
        parsed = parse_myanmar_character_message(message, super_zeko_src)
        if parsed.name or parsed.card_id:
            return parsed

    parsed = parse_caption_text_from_message(message)
    if parsed.command_name:
        parsed.source_key = get_default_source_key_from_command(parsed.command_name)
    return finalize_parsed_text(parsed)


# -----------------------------------------------------
# DB logic
# -----------------------------------------------------

async def ensure_item_indexes(collection) -> None:
    # Legacy exact indexes remain for current Lookup compatibility.
    await collection.create_index("file_unique_id", unique=True, sparse=True)
    await collection.create_index("sha256", unique=True, sparse=True)

    # V3 alias / identity indexes.
    await collection.create_index("file_unique_ids")
    await collection.create_index("sha256_aliases")
    await collection.create_index("item_key")

    await collection.create_index("media_type")
    await collection.create_index("normalized_name")
    await collection.create_index("name_aliases")
    await collection.create_index("command_name")
    await collection.create_index("source_key")
    await collection.create_index("source_bot_key")
    await collection.create_index("card_id")

    # Fingerprint lookup helpers.
    await collection.create_index("photo_fingerprint.phash")
    await collection.create_index("photo_fingerprint.pixel_sha256")
    await collection.create_index("video_fingerprint.video_signature")

    # Forward origin / archive exact lookup helpers.
    await collection.create_index(
        [("source_origin.chat_id", 1), ("source_origin.message_id", 1)],
        sparse=True,
    )
    await collection.create_index("archive.message_id", sparse=True)
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
    await user_modes.update_one({"user_id": user_id}, {"$set": {"user_id": user_id, "autosave_enabled": enabled, "updated_at": datetime.now(timezone.utc)}}, upsert=True)


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
        old_name = clean_value(update.old_name)
        new_name = clean_value(update.new_name)
        result = await collection.update_one(
            {"normalized_name": normalize_name(old_name)},
            {
                "$set": {
                    "name": new_name,
                    "normalized_name": normalize_name(new_name),
                    "updated_at": datetime.now(timezone.utc),
                    "last_source_update": update.raw_text,
                },
                "$addToSet": {"name_aliases": old_name},
            },
        )
        if result.modified_count:
            return True, f"Renamed: {update.old_name} → {update.new_name}"
        return False, f"Rename target not found: {update.old_name}"

    if update.update_type == "rarity" and update.old_name and update.new_rarity:
        new_rarity = clean_rarity_value(update.new_rarity)
        result = await collection.update_one(
            {"normalized_name": normalize_name(update.old_name)},
            {
                "$set": {
                    "rarity": new_rarity,
                    "updated_at": datetime.now(timezone.utc),
                    "last_source_update": update.raw_text,
                }
            },
        )
        if result.modified_count:
            return True, f"Rarity updated: {update.old_name} → {new_rarity}"
        return False, f"Rarity update target not found: {update.old_name}"

    return False, "Invalid update message"


async def upsert_item(
    *,
    meta: MediaMeta,
    parsed: ParsedText,
    saved_by: int,
    source_message: Optional[Message] = None,
) -> tuple[dict[str, Any], bool]:
    command_name = clean_command_name(parsed.command_name or DEFAULT_COMMAND)
    source_key = parsed.source_key or get_default_source_key_from_command(command_name)
    src = SOURCE_BY_KEY.get(source_key)
    collection = get_source_collection(source_key)

    rarity_value = clean_value(parsed.rarity or "") if (src is None or src.save_rarity) else ""
    normalized = normalize_name(parsed.name or "")
    card_id = clean_value(parsed.card_id or "")

    # Card ID is preferred as stable per-source identity. Name-only sources
    # fall back to normalized name so media variants of the same card can merge.
    item_key = (
        f"{source_key}:{card_id}"
        if card_id
        else f"{source_key}:name:{normalized}"
    )

    source_origin = (
        get_forward_source_info(source_message)
        if source_message
        else {
            "chat_id": None,
            "message_id": None,
            "user_id": None,
            "username": "",
            "title": "",
            "origin_type": "",
        }
    )

    doc = {
        "schema_version": MEDIA_SCHEMA_VERSION,
        "fingerprint_version": meta.fingerprint_version,
        "photo_hash_version": PHOTO_HASH_VERSION if meta.media_type == "photo" else "",
        "video_hash_version": VIDEO_HASH_VERSION if meta.media_type == "video" else "",
        "item_key": item_key,
        "name": clean_value(parsed.name or ""),
        "normalized_name": normalized,
        "anime_name": clean_value(parsed.anime_name or ""),
        "rarity": rarity_value,
        "card_id": card_id,
        "command_name": command_name,
        "source_key": source_key,
        "source_bot_key": source_key,
        "source_collection": collection.name,
        "source_origin": source_origin,
        "raw_text": parsed.raw_text,
        "media_type": meta.media_type,

        # Legacy single-value fields kept for current Lookup compatibility.
        "file_id": meta.file_id,
        "file_unique_id": meta.file_unique_id,
        "sha256": meta.sha256,
        "phash": meta.phash,
        "frame_hashes": meta.frame_hashes,

        # V3 fields.
        "media_geometry": meta.media_geometry,
        "photo_fingerprint": meta.photo_fingerprint,
        "video_fingerprint": meta.video_fingerprint,

        "saved_by": saved_by,
        "updated_at": datetime.now(timezone.utc),
    }

    exact_filters: list[dict[str, Any]] = []
    if meta.file_unique_id:
        exact_filters.extend(
            [
                {"file_unique_id": meta.file_unique_id},
                {"file_unique_ids": meta.file_unique_id},
            ]
        )
    if meta.sha256:
        exact_filters.extend(
            [
                {"sha256": meta.sha256},
                {"sha256_aliases": meta.sha256},
            ]
        )

    existing = None
    if exact_filters:
        existing = await collection.find_one({"$or": exact_filters})

    # Stable identity fallback solves re-upload/re-compression variants where
    # both Telegram UID and byte SHA changed.
    if not existing and item_key:
        existing = await collection.find_one({"item_key": item_key})

    aliases_to_add: dict[str, Any] = {}
    if meta.file_id:
        aliases_to_add["file_ids"] = meta.file_id
    if meta.file_unique_id:
        aliases_to_add["file_unique_ids"] = meta.file_unique_id
    if meta.sha256:
        aliases_to_add["sha256_aliases"] = meta.sha256

    if existing:
        update_doc: dict[str, Any] = {"$set": doc}
        if aliases_to_add:
            update_doc["$addToSet"] = dict(aliases_to_add)

        old_name = clean_value(existing.get("name") or "")
        new_name = clean_value(doc.get("name") or "")
        if old_name and new_name and normalize_name(old_name) != normalize_name(new_name):
            update_doc.setdefault("$addToSet", {})["name_aliases"] = old_name

        await collection.update_one({"_id": existing["_id"]}, update_doc)
        existing.update(doc)

        # Keep returned document in sync for reply/log formatting.
        for key, value in aliases_to_add.items():
            values = list(existing.get(key) or [])
            if value and value not in values:
                values.append(value)
            existing[key] = values
        return existing, False

    doc["file_ids"] = [meta.file_id] if meta.file_id else []
    doc["file_unique_ids"] = [meta.file_unique_id] if meta.file_unique_id else []
    doc["sha256_aliases"] = [meta.sha256] if meta.sha256 else []
    doc["name_aliases"] = []
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


def _photo_fingerprint(data: bytes) -> tuple[str, dict[str, Any], dict[str, Any]]:
    with Image.open(BytesIO(data)) as opened:
        image = ImageOps.exif_transpose(opened).convert("RGB")
        width, height = image.size

        # Metadata/container differences do not affect this decoded-pixel hash.
        pixel_material = (
            width.to_bytes(4, "big")
            + height.to_bytes(4, "big")
            + image.tobytes()
        )
        pixel_sha256 = hashlib.sha256(pixel_material).hexdigest()

        phash = str(imagehash.phash(image))
        fingerprint = {
            "pixel_sha256": pixel_sha256,
            "phash": phash,
            "phash_large": str(imagehash.phash(image, hash_size=16)),
            "dhash": str(imagehash.dhash(image)),
            "whash": str(imagehash.whash(image)),
            "colorhash": str(imagehash.colorhash(image)),
            "crop_hash": str(imagehash.crop_resistant_hash(image)),
        }

        geometry = {
            "width": width,
            "height": height,
            "aspect_ratio": round(width / height, 8) if height else 0.0,
            "orientation": (
                "square"
                if width == height
                else ("landscape" if width > height else "portrait")
            ),
            "file_size": len(data),
            "mime_type": (
                Image.MIME.get(opened.format, "image/jpeg")
                if opened.format
                else "image/jpeg"
            ),
        }
        return phash, fingerprint, geometry


def compute_photo_phash(data: bytes) -> str:
    phash, _fingerprint, _geometry = _photo_fingerprint(data)
    return phash


def _frame_hash_bundle(frame) -> dict[str, str]:
    rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
    image = Image.fromarray(rgb)
    return {
        "phash": str(imagehash.phash(image)),
        "dhash": str(imagehash.dhash(image)),
    }


def _read_frame_hash(
    cap,
    frame_count: int,
    position: float,
) -> Optional[dict[str, Any]]:
    # Use the same int(total * pct) rule that Lookup uses.
    idx = max(0, min(frame_count - 1, int(frame_count * position)))
    cap.set(cv2.CAP_PROP_POS_FRAMES, idx)
    ok, frame = cap.read()
    if not ok or frame is None:
        return None

    bundle = _frame_hash_bundle(frame)
    return {
        "position": round(position, 4),
        "frame_index": idx,
        **bundle,
    }


def compute_video_fingerprint(
    data: bytes,
) -> tuple[list[str], dict[str, Any], dict[str, Any]]:
    with tempfile.NamedTemporaryFile(suffix=".mp4", delete=True) as tmp:
        tmp.write(data)
        tmp.flush()

        cap = cv2.VideoCapture(tmp.name)
        if not cap.isOpened():
            raise RuntimeError("Failed to open video")

        try:
            frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0)
            fps = float(cap.get(cv2.CAP_PROP_FPS) or 0.0)
            width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH) or 0)
            height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT) or 0)

            if frame_count <= 0:
                raise RuntimeError("Video contains no readable frames")

            legacy_hashes: list[str] = []
            for position in VIDEO_LEGACY_SAMPLE_POINTS:
                sample = _read_frame_hash(cap, frame_count, position)
                if sample:
                    legacy_hashes.append(sample["phash"])

            samples: list[dict[str, Any]] = []
            for position in VIDEO_V3_SAMPLE_POINTS:
                sample = _read_frame_hash(cap, frame_count, position)
                if sample:
                    samples.append(sample)

            if not legacy_hashes and not samples:
                raise RuntimeError("Could not extract frames from video")

            signature_material = "|".join(
                f"{sample['position']}:{sample['phash']}:{sample['dhash']}"
                for sample in samples
            ).encode("utf-8")
            video_signature = (
                hashlib.sha256(signature_material).hexdigest()
                if signature_material
                else ""
            )

            duration_ms = (
                int(round((frame_count / fps) * 1000))
                if fps > 0
                else 0
            )

            fingerprint = {
                "duration_ms": duration_ms,
                "fps": round(fps, 6),
                "frame_count": frame_count,
                "width": width,
                "height": height,
                "sample_hashes": samples,
                "video_signature": video_signature,
            }

            geometry = {
                "width": width,
                "height": height,
                "aspect_ratio": round(width / height, 8) if height else 0.0,
                "orientation": (
                    "square"
                    if width == height
                    else ("landscape" if width > height else "portrait")
                ),
                "file_size": len(data),
                "mime_type": "video/mp4",
                "duration_ms": duration_ms,
                "fps": round(fps, 6),
                "frame_count": frame_count,
            }
            return legacy_hashes, fingerprint, geometry
        finally:
            cap.release()


def compute_video_hashes(data: bytes) -> list[str]:
    hashes, _fingerprint, _geometry = compute_video_fingerprint(data)
    return hashes


async def get_media_meta(bot: Bot, message: Message) -> MediaMeta:
    media_type, media = extract_media_handle(message)
    if not media_type or not media:
        raise ValueError("Message does not contain supported media")

    raw = await download_file_bytes(bot, media.file_id)
    digest = sha256_hex(raw)

    if media_type == "photo":
        phash, photo_fingerprint, geometry = _photo_fingerprint(raw)
        if getattr(media, "file_size", None):
            geometry["telegram_file_size"] = int(media.file_size)

        return MediaMeta(
            media_type="photo",
            file_id=media.file_id,
            file_unique_id=media.file_unique_id,
            sha256=digest,
            phash=phash,
            media_geometry=geometry,
            photo_fingerprint=photo_fingerprint,
        )

    frame_hashes, video_fingerprint, geometry = compute_video_fingerprint(raw)

    mime_type = str(getattr(media, "mime_type", "") or "")
    if mime_type:
        geometry["mime_type"] = mime_type
    if getattr(media, "file_size", None):
        geometry["telegram_file_size"] = int(media.file_size)

    return MediaMeta(
        media_type="video",
        file_id=media.file_id,
        file_unique_id=media.file_unique_id,
        sha256=digest,
        frame_hashes=frame_hashes,
        media_geometry=geometry,
        video_fingerprint=video_fingerprint,
    )

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



def get_log_channel_for_source(source_key: str):
    return SOURCE_LOG_CHANNELS.get(source_key) or ADDED_LOG_CHANNEL


async def send_added_log(
    *,
    bot: Bot,
    source_message: Message,
    doc: dict[str, Any],
    created: bool,
    mode: str,
    source_label: str,
    added_by_user,
) -> Optional[dict[str, Any]]:
    source_key = clean_value(str(doc.get("source_key") or ""))
    target_log_channel = get_log_channel_for_source(source_key)
    if not target_log_channel:
        return None

    media_type, media = extract_media_handle(source_message)
    if not media_type or not media:
        return None

    caption = build_added_log_caption(
        doc=doc,
        created=created,
        mode=mode,
        source_label=source_label,
        added_by_user=added_by_user,
    )

    if media_type == "photo":
        archived_message = await bot.send_photo(
            chat_id=target_log_channel,
            photo=media.file_id,
            caption=caption,
            parse_mode=ParseMode.HTML,
        )
    else:
        archived_message = await bot.send_video(
            chat_id=target_log_channel,
            video=media.file_id,
            caption=caption,
            parse_mode=ParseMode.HTML,
        )

    _archive_type, archive_media = extract_media_handle(archived_message)
    return {
        "chat_id": int(archived_message.chat.id),
        "message_id": int(archived_message.message_id),
        "file_id": getattr(archive_media, "file_id", "") if archive_media else "",
        "file_unique_id": (
            getattr(archive_media, "file_unique_id", "")
            if archive_media
            else ""
        ),
        "archived_at": datetime.now(timezone.utc),
    }


async def persist_archive_pointer(
    doc: dict[str, Any],
    archive: Optional[dict[str, Any]],
) -> None:
    if not archive or not doc.get("_id") or not doc.get("source_collection"):
        return

    update: dict[str, Any] = {
        "$set": {
            "archive": archive,
            "archive_chat_id": archive.get("chat_id"),
            "archive_message_id": archive.get("message_id"),
            "updated_at": datetime.now(timezone.utc),
        }
    }

    add_to_set: dict[str, Any] = {}
    if archive.get("file_id"):
        add_to_set["file_ids"] = archive["file_id"]
    if archive.get("file_unique_id"):
        add_to_set["file_unique_ids"] = archive["file_unique_id"]
    if add_to_set:
        update["$addToSet"] = add_to_set

    await db[str(doc["source_collection"])].update_one(
        {"_id": doc["_id"]},
        update,
    )

    doc["archive"] = archive
    doc["archive_chat_id"] = archive.get("chat_id")
    doc["archive_message_id"] = archive.get("message_id")

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
        "• /checkinline @source_bot\n"
        "• /addsudo /rmsudo\n\n"
        "အသစ်ထည့်ထားသော inline source:\n"
        "• @roronoa_zoro_robot → name only\n"
        "• @character_picker_bot → name + id + rarity\n"
        "• @BikaCharacterBot → name + id + rarity + anime (/bika)\n"
        "• @SenpaiCatcherBot → video/photo + name + id + rarity + anime (/pick)\n"
        "• @Super_zeko_bot → photo/video + name + id + rarity + anime (/ziceko)\n"
        "• @ImmortalDonghuaBot → photo/video + name + id + rarity + anime (/dao)\n"
        "• @orinx_catcher_waifu_bot → photo/video + name + id + rarity + series (/orin)\n"
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
        f"‣ Default Log Channel : <code>{html_escape(ADDED_LOG_CHANNEL or '-')}</code>",
        f"‣ Routed Log Channels : <b>{len(SOURCE_LOG_CHANNELS)}</b>",
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
        process = await asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
        stdout, stderr = await process.communicate()
        logger.warning("PM2 restart finished | returncode=%s | stdout=%s | stderr=%s", process.returncode, stdout.decode(errors="ignore")[:1000], stderr.decode(errors="ignore")[:1000])
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
        await message.reply("Telegram restart is disabled.\n\nEnable with:\n<code>ENABLE_TELEGRAM_RESTART=true</code>", parse_mode=ParseMode.HTML)
        return
    await message.reply(f"♻️ Restarting bot with PM2...\nProcess: <code>{html_escape(PM2_PROCESS_NAME)}</code>", parse_mode=ParseMode.HTML)
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


@router.message(Command("checkinline"))
async def checkinline_handler(message: Message, command: CommandObject) -> None:
    await remember_chat(message)
    if not await can_save(message):
        return
    src = resolve_source_from_arg(command.args)
    if not src:
        await message.reply("အသုံးပြုပုံ:\n/checkinline @roronoa_zoro_robot\n/checkinline @character_picker_bot\n/checkinline @BikaCharacterBot\n/checkinline @orinx_catcher_waifu_bot\n/checkinline @ImmortalDonghuaBot\n/checkinline roronoa_zoro\n/checkinline character_picker\n/checkinline bika_character\n/checkinline orinx_waifu\n/checkinline immortal_donghua")
        return
    if not ADD_HELPER.enabled or not ADD_HELPER.client:
        await message.reply("/checkinline သုံးရန် ADD_HELPER_ENABLED=true နှင့် Pyrogram SESSION_STRING လိုပါတယ်။")
        return
    notice = await message.reply(f"🔎 Checking inline results...\nSource: <code>{html_escape(src.bot_username)}</code>", parse_mode=ParseMode.HTML)
    try:
        total, pages, stopped_reason = await ADD_HELPER.count_inline_results(src.bot_username, max_pages=CHECKINLINE_MAX_PAGES)
    except Exception as exc:
        logger.exception("checkinline failed")
        await notice.edit_text(f"❌ checkinline failed\nSource: <code>{html_escape(src.bot_username)}</code>\nError: {html_escape(str(exc))}", parse_mode=ParseMode.HTML)
        return
    await notice.edit_text(
        f"✅ <b>Inline Result Check</b>\n\n"
        f"Source: <code>{html_escape(src.bot_username)}</code>\n"
        f"Key: <code>{html_escape(src.key)}</code>\n"
        f"Total result: <b>{total}</b>\n"
        f"Pages checked: <b>{pages}</b>\n"
        f"Status: <code>{html_escape(stopped_reason)}</code>",
        parse_mode=ParseMode.HTML,
    )


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
        doc, created = await upsert_item(meta=meta, parsed=parsed, saved_by=message.from_user.id, source_message=target)
    except Exception as exc:
        logger.exception("save failed")
        await message.reply(f"save မအောင်မြင်ပါ: {html_escape(str(exc))}", parse_mode=ParseMode.HTML)
        return
    try:
        archive = await send_added_log(bot=bot, source_message=target, doc=doc, created=created, mode="manual-save", source_label=get_log_source_label(target), added_by_user=message.from_user)
        await persist_archive_pointer(doc, archive)
    except Exception:
        logger.exception("added log send failed")
    status = "Saved" if created else "Updated"
    await message.reply(
        f"{status}: <b>{html_escape(doc['name'])}</b>\n"
        f"ID: <b>{html_escape(doc.get('card_id') or '-')}</b>\n"
        f"Rarity: <b>{html_escape(doc.get('rarity') or '-')}</b>\n"
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
        doc, created = await upsert_item(meta=meta, parsed=parsed, saved_by=(message.from_user.id if message.from_user else 0), source_message=message)
        source_label = get_autosave_source_label(message)
        try:
            archive = await send_added_log(bot=bot, source_message=message, doc=doc, created=created, mode=mode, source_label=str(source_label), added_by_user=message.from_user)
            await persist_archive_pointer(doc, archive)
        except Exception:
            logger.exception("added log send failed")
        status = "Saved" if created else "Updated"
        await message.reply(
            f"{status}: <b>{html_escape(doc['name'])}</b>\n"
            f"ID: <b>{html_escape(doc.get('card_id') or '-')}</b>\n"
            f"Rarity: <b>{html_escape(doc.get('rarity') or '-')}</b>\n"
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
    supported_source = bool(
        is_allowed_forward_source(message)
        or get_inline_source_command(message)
        or get_sender_source_def(message)
        or looks_like_myanmar_character_source(message)
    )

    if is_default_target_chat(message):
        target_chat_autosave_enabled = await get_target_chat_autosave_mode(message.chat.id)
        if not target_chat_autosave_enabled or not supported_source:
            return
        await autosave_media(message, bot, "target-auto-save")
        return

    if is_private_chat(message) and user_can_save and autosave_enabled:
        if not supported_source:
            if is_forwarded_message(message):
                await message.reply("ဒီ forwarded source ကို auto-save ခွင့်မပြုထားသေးပါဘူး။")
            return
        await autosave_media(message, bot, "auto-save")




# -----------------------------------------------------
# DM crawler owner controls
# -----------------------------------------------------
async def _dm_start(message: Message, key: str, command: CommandObject=None):
    if message.from_user and message.from_user.id not in OWNER_IDS:
        return
    await HELPER_CONTROLLER.start(key, 1, HELPER_RUNTIME.client, DEFAULT_TARGET_CHAT)
    await message.reply(f"DM helper started: {key}")

async def _dm_resume(message: Message, key: str, command: CommandObject):
    if message.from_user and message.from_user.id not in OWNER_IDS:
        return
    if not command.args or not command.args.strip().isdigit():
        await message.reply("Usage: /resumedm... ID")
        return
    await HELPER_CONTROLLER.resume(key, int(command.args), HELPER_RUNTIME.client, DEFAULT_TARGET_CHAT)
    await message.reply(f"DM helper resumed: {key} ID {command.args}")

@router.message(Command("startdmcatchbot"))
async def startdmcatch(message: Message): await _dm_start(message, "catch")

@router.message(Command("startdmgrabbot"))
async def startdmgrab(message: Message): await _dm_start(message, "grab")

@router.message(Command("startdmsenpaibot"))
async def startdmsenpai(message: Message): await _dm_start(message, "senpai")

@router.message(Command("startdmhallowbot"))
async def startdmhallow(message: Message): await _dm_start(message, "hallow")

@router.message(Command("startdmtakersbot"))
async def startdmtakers(message: Message): await _dm_start(message, "takers")

@router.message(Command("resumedmcatchbot"))
async def resumedmcatch(message: Message, command: CommandObject): await _dm_resume(message,"catch",command)

@router.message(Command("resumedmgrabbot"))
async def resumedmgrab(message: Message, command: CommandObject): await _dm_resume(message,"grab",command)

@router.message(Command("resumedmsenpaibot"))
async def resumedmsenpai(message: Message, command: CommandObject): await _dm_resume(message,"senpai",command)

@router.message(Command("resumedmhallowbot"))
async def resumedmhallow(message: Message, command: CommandObject): await _dm_resume(message,"hallow",command)

@router.message(Command("resumedmtakersbot"))
async def resumedmtakers(message: Message, command: CommandObject): await _dm_resume(message,"takers",command)

@router.message(Command("stopdm"))
async def stop_dm(message: Message):
    if message.from_user and message.from_user.id not in OWNER_IDS:
        return
    await HELPER_CONTROLLER.stop_all_dm()
    await message.reply("All DM helpers stopped.")

# -----------------------------------------------------
# Webhook / runner
# -----------------------------------------------------
def normalize_webhook_path(path: str) -> str:
    return path if path.startswith("/") else f"/{path}"


async def on_startup(bot: Bot) -> None:
    await HELPER_RUNTIME.start(HELPER_CONTROLLER)
    await ensure_indexes()
    await bot.set_my_commands(
        [
            BotCommand(command="start", description="Start the adding bot"),
            BotCommand(command="status", description="Show adding bot status"),
            BotCommand(command="stats", description="Show adding bot stats"),
            BotCommand(command="autosave", description="Auto-save on/off/status"),
            BotCommand(command="save", description="Save replied media"),
            BotCommand(command="checkinline", description="Check source inline total result"),
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
    logger.info("Forward chat ids: %s", sorted(SOURCE_BY_FORWARD_CHAT_ID.keys()))
    logger.info("Default added log channel: %s", ADDED_LOG_CHANNEL or "none")
    logger.info("Source log channels: %s", SOURCE_LOG_CHANNELS)
    logger.info("Senpai forward source: %s | bot_id=%s", SENPAI_FORWARD_CHAT_DEFAULT, SENPAI_BOT_ID)
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
    "roronoa_zoro": os.getenv("RORONOA_ZORO_INLINE_BOT", "@roronoa_zoro_robot"),
    "character_picker": os.getenv("CHARACTER_PICKER_INLINE_BOT", "@character_picker_bot"),
    "super_zeko": os.getenv("SUPER_ZEKO_INLINE_BOT", "@Super_zeko_bot"),
    "orinx_waifu": os.getenv("ORINX_INLINE_BOT", "@orinx_catcher_waifu_bot"),
    "immortal_donghua": os.getenv("IMMORTAL_DONGHUA_INLINE_BOT", "@ImmortalDonghuaBot"),
}
# Senpai DB forward source is built in, so VPS env does NOT need FW_SENPAI_SOURCE_CHAT.
# Env override is still supported if you ever change the channel later.
SENPAI_FORWARD_CHAT_USERNAME = "@fafafawfawfa"
SENPAI_FORWARD_CHAT_DEFAULT = SENPAI_FORWARD_CHAT_USERNAME

ADD_HELPER_FORWARD_OVERRIDES = {
    "character_seizer": os.getenv("FW_SEIZER_SOURCE_CHAT", "@Seizer_Database"),
    "capture_character": os.getenv("FW_CAPTURE_SOURCE_CHAT", "@CaptureDatabase"),
    "characters_hallow": os.getenv("FW_HALLOW_SOURCE_CHAT", "@hallowuploads"),
    "waifux_grab": os.getenv("FW_WAIFUX_SOURCE_CHAT", os.getenv("FW_WAIFUX_GRAB_SOURCE_CHAT", "@WAIFUXGRAB_DATABASE")),
    "bika_character": os.getenv("FW_BIKA_SOURCE_CHAT", os.getenv("FW_BIKA_CHARACTER", "-1003923540741")),
    "senpai_catcher": os.getenv("FW_SENPAI_SOURCE_CHAT", os.getenv("FW_SENPAI_SOURCE", SENPAI_FORWARD_CHAT_DEFAULT)),
    "super_zeko": os.getenv("FW_SUPER_ZEKO_SOURCE_CHAT", os.getenv("FW_ZICEKO_SOURCE_CHAT", "@zicekodata_1")),
    "orinx_waifu": os.getenv("FW_ORINX_SOURCE_CHAT", os.getenv("FW_ORIN_SOURCE_CHAT", "@timunagalaya")),
    "immortal_donghua": os.getenv("FW_IMMORTAL_DONGHUA_SOURCE_CHAT", os.getenv("FW_DONGHUA_SOURCE_CHAT", "-1004397263975")),
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
    AddHelperSource(
        "waifux_grab",
        "Waifux Grab",
        _env_inline("waifux_grab", "@WaifuxGrabBot"),
        ("/startwaifuxgrabbot", "/startwaifuxgrab", "/startwaifux", "/start_waifux"),
        ("/resumewaifuxgrabbot", "/resumewaifuxgrab", "/resumewaifux", "/resume_waifux"),
        _env_forward("waifux_grab", "@WAIFUXGRAB_DATABASE"),
        ("/startfwwaifuxgrabbot", "/startfwwaifuxgrab", "/startfwwaifux", "/start_fw_waifux"),
        ("/resumefwwaifuxgrabbot", "/resumefwwaifuxgrab", "/resumefwwaifux", "/resume_fw_waifux"),
    ),
    AddHelperSource("catch_your_waifu", "Catch Your Waifu", _env_inline("catch_your_waifu", "@Catch_Your_Waifu_Bot"), ("/startcatchyourwaifubot", "/startcatchyourwaifu", "/start_catch_your_waifu"), ("/resumecatchyourwaifubot", "/resumecatchyourwaifu", "/resume_catch_your_waifu")),
    AddHelperSource("waifu_grabber", "Waifu Grabber", _env_inline("waifu_grabber", "@Waifu_Grabber_Bot"), ("/startwaifugrabberbot", "/startwaifugrabber", "/start_waifu_grabber"), ("/resumewaifugrabberbot", "/resumewaifugrabber", "/resume_waifu_grabber")),
    AddHelperSource("roronoa_zoro", "Roronoa Zoro", _env_inline("roronoa_zoro", "@roronoa_zoro_robot"), ("/startzorobot", "/startzoro", "/start_roronoa_zoro"), ("/resumezorobot", "/resumezoro", "/resume_roronoa_zoro")),
    AddHelperSource("character_picker", "Character Picker", _env_inline("character_picker", "@character_picker_bot"), ("/startpickerbot", "/startpicker", "/start_character_picker"), ("/resumepickerbot", "/resumepicker", "/resume_character_picker")),
    AddHelperSource(
        "senpai_catcher",
        "SenpaiCatcher DB",
        _env_inline("senpai_catcher", "@SenpaiCatcherBot"),
        ("/startsenpaibot", "/start_senpai_bot"),
        ("/resumesenpaibot", "/resume_senpai_bot"),
        _env_forward("senpai_catcher", SENPAI_FORWARD_CHAT_DEFAULT),
        ("/startfwsenpaibot", "/startfwsenpai", "/start_fw_senpai"),
        ("/resumefwsenpaibot", "/resumefwsenpai", "/resume_fw_senpai"),
    ),
    AddHelperSource(
        "bika_character",
        "Bika Character",
        _env_inline("bika_character", "@BikaCharacterBot"),
        ("/startbika", "/startbikabot", "/start_bika"),
        ("/resumebika", "/resumebikabot", "/resume_bika"),
        _env_forward("bika_character", "-1003923540741"),
        ("/startfwbika", "/startfwbikabot", "/start_fw_bika"),
        ("/resumefwbika", "/resumefwbikabot", "/resume_fw_bika"),
    ),
    AddHelperSource(
        "super_zeko",
        "Super Zeko / Myanmar Character Logs",
        _env_inline("super_zeko", "@Super_zeko_bot"),
        ("/startzicekobot", "/startziceko", "/start_super_zeko"),
        ("/resumezicekobot", "/resumeziceko", "/resume_super_zeko"),
        _env_forward("super_zeko", "@zicekodata_1"),
        ("/startfwzicekobot", "/startfwziceko", "/start_fw_ziceko"),
        ("/resumefwzicekobot", "/resumefwziceko", "/resume_fw_ziceko"),
    ),
    AddHelperSource(
        "orinx_waifu",
        "OrinX Waifu / OrinX Logs",
        _env_inline("orinx_waifu", "@orinx_catcher_waifu_bot"),
        ("/startorinbot", "/startorin", "/start_orin", "/start_orinx"),
        ("/resumeorinbot", "/resumeorin", "/resume_orin", "/resume_orinx"),
        _env_forward("orinx_waifu", "@timunagalaya"),
        ("/startfworinbot", "/startfworin", "/start_fw_orin", "/startfworinx"),
        ("/resumefworinbot", "/resumefworin", "/resume_fw_orin", "/resumefworinx"),
    ),
    AddHelperSource(
        "immortal_donghua",
        "Immortal Donghua / Donghua Database Channel",
        _env_inline("immortal_donghua", "@ImmortalDonghuaBot"),
        ("/startdaobot", "/startdao", "/start_dao", "/startdonghua"),
        ("/resumedaobot", "/resumedao", "/resume_dao", "/resumedonghua"),
        _env_forward("immortal_donghua", "-1004397263975"),
        ("/startfwdaobot", "/startfwdao", "/start_fw_dao", "/startfwdonghua"),
        ("/resumefwdaobot", "/resumefwdao", "/resume_fw_dao", "/resumefwdonghua"),
    ),
]

ADD_HELPER_START_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_RESUME_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_FW_START_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_FW_RESUME_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_FW_VIDEO_START_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_FW_VIDEO_RESUME_COMMANDS: dict[str, AddHelperSource] = {}
ADD_HELPER_BY_KEY = {src.key: src for src in ADD_HELPER_SOURCES}
ADD_HELPER_BY_INLINE = {norm_username(src.inline_bot): src for src in ADD_HELPER_SOURCES}

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
            ADD_HELPER_FW_VIDEO_START_COMMANDS[_cmd.replace("/startfw", "/startfwvideo", 1)] = _src
            ADD_HELPER_FW_VIDEO_START_COMMANDS[_cmd.replace("bot", "videobot")] = _src
        for _cmd in _src.forward_resume_aliases:
            ADD_HELPER_FW_VIDEO_RESUME_COMMANDS[_cmd.replace("/resumefw", "/resumefwvideo", 1)] = _src
            ADD_HELPER_FW_VIDEO_RESUME_COMMANDS[_cmd.replace("bot", "videobot")] = _src


def add_helper_clean(value: str) -> str:
    return " ".join((value or "").split()).strip()


def add_helper_chat_ref(value):
    """Pyrogram accepts usernames and integer chat ids. Convert numeric strings."""
    if isinstance(value, int):
        return value
    value = add_helper_clean(str(value or ""))
    if value.lstrip("-").isdigit():
        return int(value)
    return value


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
        raise ValueError("Resume count is required. Example: /resumepickerbot 1000 5")
    count = int(parts[1])
    delay = default_delay
    if len(parts) >= 3:
        if not parts[2].isdigit():
            raise ValueError("Delay must be a number")
        delay = int(parts[2])
    return count, delay


def add_helper_state_path() -> Path:
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
    for key in ["runner_mode", "source_ref", "target_chat", "current_offset", "current_index", "sent_count", "skipped_count", "delay_seconds", "resume_target_count"]:
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
    skipped_count: int = 0
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

    def _load_progress(self, runner_mode: str, source_ref: str) -> tuple[str, int, int, int, int]:
        data = add_helper_load_state()
        if data.get("runner_mode") != runner_mode or data.get("source_ref") != source_ref:
            return "", 0, 0, 0, 0
        return (
            str(data.get("current_offset") or ""),
            int(data.get("current_index") or 0),
            int(data.get("sent_count") or 0),
            int(data.get("skipped_count") or 0),
            int(data.get("resume_target_count") or data.get("sent_count") or 0),
        )

    def _save_progress(self, source_ref: str, offset: str, index: int) -> None:
        data = add_helper_load_state()
        data.update({"runner_mode": self.state.runner_mode, "source_ref": source_ref, "target_chat": str(self.resolved_target_chat), "current_offset": offset, "current_index": index, "sent_count": self.state.sent_count, "skipped_count": self.state.skipped_count, "delay_seconds": self.state.delay_seconds, "resume_target_count": self.state.resume_target_count})
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
            except (RPCError, OSError, TimeoutError, ValueError) as e:
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

    async def count_inline_results(self, source_bot: str, max_pages: int = CHECKINLINE_MAX_PAGES) -> tuple[int, int, str]:
        if not self.enabled or not self.client:
            raise RuntimeError("AddHelper client is not running")
        offset = ""
        total = 0
        pages = 0
        seen_offsets: set[str] = set()
        while True:
            if pages >= max_pages:
                return total, pages, f"stopped at max_pages={max_pages}"
            offset_key = offset or "<first>"
            if offset_key in seen_offsets:
                return total, pages, "stopped because next_offset looped"
            seen_offsets.add(offset_key)
            results = await self._get_inline_results(source_bot, offset)
            page_len = len(getattr(results, "results", []) or [])
            total += page_len
            pages += 1
            next_offset = getattr(results, "next_offset", "") or ""
            if page_len <= 0:
                return total, pages, "finished: empty page"
            if not next_offset:
                return total, pages, "finished: no next_offset"
            offset = next_offset

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
            offset, index, sent_count, skipped_count, target_count = self._load_progress("inline", source_bot)
        else:
            offset, index = await self._locate_inline_cursor(source_bot, resume_count)
            sent_count = resume_count
            skipped_count = 0
            target_count = resume_count
        self.runner_stop_event = asyncio.Event()
        self.state = AddHelperRunnerState(True, "inline", sent_count, skipped_count, delay_seconds, self.resolved_target_chat, offset, index, "", source_bot, target_count)
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
                    try:
                        await self._send_inline_result(source_bot, results, result.id)
                        self.state.sent_count += 1
                        logger.info("AddHelper sent #%s inline result from %s", self.state.sent_count, source_bot)
                    except asyncio.CancelledError:
                        raise
                    except Exception as e:
                        # Auto-skip inline send failures and keep going.
                        self.state.skipped_count += 1
                        self.state.last_error = f"Skipped result index={idx}: {e}"
                        logger.exception("AddHelper skipped inline result from %s index=%s", source_bot, idx)
                    finally:
                        self.state.current_offset = offset
                        self.state.current_index = idx + 1
                        self._save_progress(source_bot, offset, idx + 1)
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
        source_chat_ref = add_helper_chat_ref(source_chat)
        async for msg in self.client.get_chat_history(source_chat_ref):
            document = getattr(msg, "document", None)
            has_photo = bool(getattr(msg, "photo", None))
            has_video = bool(getattr(msg, "video", None) or getattr(msg, "animation", None) or (document and str(getattr(document, "mime_type", "") or "").startswith("video/")))
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
                await self.client.forward_messages(chat_id=self.resolved_target_chat, from_chat_id=add_helper_chat_ref(source_chat), message_ids=message_id)
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
            _, index, sent_count, skipped_count, target_count = self._load_progress(progress_mode, source_chat)
        else:
            index = resume_count
            sent_count = resume_count
            skipped_count = 0
            target_count = resume_count
        if index >= len(media_ids):
            raise RuntimeError(f"Resume index {index} is at/after the end ({len(media_ids)})")
        self.runner_stop_event = asyncio.Event()
        self.state = AddHelperRunnerState(True, progress_mode, sent_count, skipped_count, delay_seconds, self.resolved_target_chat, "", index, "", source_chat, target_count)
        self._save_progress(source_chat, "", index)
        self.runner_task = asyncio.create_task(self._worker_forward(source_chat, media_ids))

    async def _worker_forward(self, source_chat: str, media_ids: list[int]):
        try:
            start_index = max(0, min(self.state.current_index or 0, len(media_ids)))
            for idx in range(start_index, len(media_ids)):
                if self.runner_stop_event.is_set():
                    break
                mid = media_ids[idx]
                try:
                    await self._forward_message(source_chat, mid)
                    self.state.sent_count += 1
                    logger.info("AddHelper forwarded #%s msg_id=%s from %s", self.state.sent_count, mid, source_chat)
                except asyncio.CancelledError:
                    raise
                except Exception as e:
                    self.state.skipped_count += 1
                    self.state.last_error = f"Skipped forward msg_id={mid}: {e}"
                    logger.exception("AddHelper skipped forward msg_id=%s from %s", mid, source_chat)
                finally:
                    self.state.current_index = idx + 1
                    self.state.current_offset = str(mid)
                    self._save_progress(source_chat, str(mid), idx + 1)
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

    async def start_senpai_command_loop(self, start_from: int, delay_seconds: int):
        if self.is_running():
            raise RuntimeError("AddHelper is already running")
        start_from = max(1, int(start_from))
        delay_seconds = max(1, min(int(delay_seconds), ADD_HELPER_MAX_SEND_DELAY))
        self.runner_stop_event = asyncio.Event()
        self.state = AddHelperRunnerState(
            True,
            "senpai_command",
            max(0, start_from - 1),
            0,
            delay_seconds,
            self.resolved_target_chat,
            "",
            start_from,
            "",
            "@SenpaiCatcherBot",
            start_from,
        )
        self._save_progress("@SenpaiCatcherBot", "", start_from)
        self.runner_task = asyncio.create_task(self._worker_senpai_command_loop(start_from))

    async def _worker_senpai_command_loop(self, start_from: int):
        current = max(1, int(start_from))
        try:
            while not self.runner_stop_event.is_set():
                try:
                    await self.client.send_message(self.resolved_target_chat, f"/c {current}")
                    self.state.sent_count += 1
                    self.state.current_index = current
                    self.state.current_offset = str(current)
                    self._save_progress("@SenpaiCatcherBot", str(current), current)
                    logger.info("Senpai command sent: /c %s", current)
                except asyncio.CancelledError:
                    raise
                except Exception as e:
                    self.state.skipped_count += 1
                    self.state.last_error = f"Senpai command /c {current} failed: {e}"
                    logger.exception("Senpai command send failed")
                current += 1
                await self._sleep_with_stop(self.state.delay_seconds)
        except Exception as e:
            self.state.last_error = str(e)
            logger.exception("Senpai command worker failed")
            await self._notify_error("senpai_command", "@SenpaiCatcherBot")
        finally:
            self.state.running = False

    async def _notify_error(self, mode: str, source: str) -> None:
        try:
            await self._reply("⚠️ AddHelper Stopped\n\n" f"Mode: {mode}\n" f"Source: {source}\n" f"Sent count: {self.state.sent_count}\n" f"Skipped count: {self.state.skipped_count}\n" f"Current offset: {self.state.current_offset or '-'}\n" f"Current index: {self.state.current_index}\n" f"Last error: {self.state.last_error or 'unknown'}")
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
        lines += ["", "Senpai command loop:", "• SenpaiCatcher: /startsenpaibot [delay] | /resumesenpaibot <start_id> [delay]"]
        lines += ["Senpai DB forward:", "• SenpaiBase: /startfwsenpaibot [delay] | /resumefwsenpaibot <count> [delay]"]
        lines += ["", "Other: /helperstatus /stophelper /resethelperprogress /checkinline <source>"]
        return "\n".join(lines)

    def _resolve_control_source(self, raw_arg: str) -> Optional[AddHelperSource]:
        arg = add_helper_clean(raw_arg)
        if not arg:
            return None
        first = arg.split()[0]
        key = first.strip().lstrip("@").casefold().replace("-", "_")
        if key in ADD_HELPER_BY_KEY:
            return ADD_HELPER_BY_KEY[key]
        inline_key = norm_username(first)
        if inline_key in ADD_HELPER_BY_INLINE:
            return ADD_HELPER_BY_INLINE[inline_key]
        source_def = resolve_source_from_arg(first)
        if source_def and source_def.key in ADD_HELPER_BY_KEY:
            return ADD_HELPER_BY_KEY[source_def.key]
        return None

    async def _execute_control_command(self, msg) -> None:
        text = add_helper_clean(getattr(msg, "text", "") or "")
        cmd = add_helper_command_name(text)
        if cmd in {"/addhelper", "/helper", "/helperstart", "/starthelper"}:
            await self._reply(self._help_text(), reply_to_message_id=msg.id)
            return
        if cmd in {"/helperstatus", "/addhelperstatus"}:
            s = self.state
            await self._reply(f"Running: {'YES' if self.is_running() else 'NO'}\nMode: {s.runner_mode or '-'}\nSource: {s.source_ref or '-'}\nTarget chat: {s.target_chat}\nDelay: {s.delay_seconds}s\nSent count: {s.sent_count}\nSkipped count: {s.skipped_count}\nCurrent offset: {s.current_offset or '-'}\nCurrent index: {s.current_index}\nResume target count: {s.resume_target_count}\nLast error: {s.last_error or '-'}", reply_to_message_id=msg.id)
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
        if cmd == "/checkinline":
            source = self._resolve_control_source(text.partition(" ")[2])
            if not source:
                await self._reply("Usage: /checkinline @source_bot\nExample: /checkinline @character_picker_bot", reply_to_message_id=msg.id)
                return
            await self._reply(f"🔎 Checking inline results...\nSource: {source.inline_bot}", reply_to_message_id=msg.id)
            total, pages, reason = await self.count_inline_results(source.inline_bot, max_pages=CHECKINLINE_MAX_PAGES)
            await self._reply(f"✅ Inline Result Check\n\nSource: {source.inline_bot}\nKey: {source.key}\nTotal result: {total}\nPages checked: {pages}\nStatus: {reason}", reply_to_message_id=msg.id)
            return
        if cmd == "/startsenpaibot":
            delay = add_helper_parse_delay(text, ADD_HELPER_DEFAULT_SEND_DELAY)
            await self.start_senpai_command_loop(1, delay)
            await self._reply(
                f"Started Senpai command loop.\nSource: @SenpaiCatcherBot\nStart: /c 1\nDelay: {delay}s",
                reply_to_message_id=msg.id,
            )
            return
        if cmd == "/resumesenpaibot":
            parts = add_helper_clean(text).split()
            if len(parts) < 2 or not parts[1].isdigit():
                await self._reply("Usage: /resumesenpaibot 300 [delay]", reply_to_message_id=msg.id)
                return
            start_from = int(parts[1])
            delay = ADD_HELPER_DEFAULT_SEND_DELAY
            if len(parts) >= 3:
                if not parts[2].isdigit():
                    await self._reply("Delay must be a number", reply_to_message_id=msg.id)
                    return
                delay = int(parts[2])
            await self.start_senpai_command_loop(start_from, delay)
            await self._reply(
                f"Resumed Senpai command loop.\nSource: @SenpaiCatcherBot\nStart: /c {start_from}\nDelay: {delay}s",
                reply_to_message_id=msg.id,
            )
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
        known = {
            "/addhelper", "/helper", "/helperstart", "/starthelper",
            "/helperstatus", "/addhelperstatus", "/stophelper", "/stopinlinebot",
            "/resethelperprogress", "/resetinlineprogress", "/checkinline",
            "/startsenpaibot", "/resumesenpaibot",
            *ADD_HELPER_START_COMMANDS.keys(), *ADD_HELPER_RESUME_COMMANDS.keys(),
            *ADD_HELPER_FW_START_COMMANDS.keys(), *ADD_HELPER_FW_RESUME_COMMANDS.keys(),
            *ADD_HELPER_FW_VIDEO_START_COMMANDS.keys(), *ADD_HELPER_FW_VIDEO_RESUME_COMMANDS.keys(),
        }
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



# ---------------- DM crawler commands ----------------
async def _dm_start(message: Message, bot: Bot, key: str):
    try:
        await DM_HELPER.start(key, 1, client=HELPER_RUNTIME.client, target_chat=DEFAULT_TARGET_CHAT)
        await message.answer(f"DM helper started: {key}")
    except Exception as e:
        await message.answer(f"DM start error: {e}")

async def _dm_resume(message: Message, bot: Bot, key: str, value: int):
    try:
        await DM_HELPER.resume(key, value, client=HELPER_RUNTIME.client, target_chat=DEFAULT_TARGET_CHAT)
        await message.answer(f"DM helper resumed: {key} {value}")
    except Exception as e:
        await message.answer(f"DM resume error: {e}")

@router.message(Command("startdmcatchbot"))
async def start_dm_catch(message: Message, bot: Bot):
    await _dm_start(message, bot, "catch")

@router.message(Command("startdmgrabbot"))
async def start_dm_grab(message: Message, bot: Bot):
    await _dm_start(message, bot, "grab")

@router.message(Command("startdmsenpaibot"))
async def start_dm_senpai(message: Message, bot: Bot):
    await _dm_start(message, bot, "senpai")

@router.message(Command("startdmhallowbot"))
async def start_dm_hallow(message: Message, bot: Bot):
    await _dm_start(message, bot, "hallow")

@router.message(Command("startdmtakersbot"))
async def start_dm_takers(message: Message, bot: Bot):
    await _dm_start(message, bot, "takers")

@router.message(Command("stopdm"))
async def stop_dm(message: Message):
    await DM_HELPER.stop_all_dm()
    await message.answer("All DM helpers stopped.")

@router.message()
async def dm_resume_commands(message: Message, bot: Bot):
    text = (message.text or "").strip().split()
    if not text:
        return
    cmd = text[0].split("@")[0]
    mapping = {
        "/resumedmcatchbot": "catch",
        "/resumedmgrabbot": "grab",
        "/resumedmsenpaibot": "senpai",
        "/resumedmhallowbot": "hallow",
        "/resumedmtakersbot": "takers",
    }
    if cmd in mapping and len(text) > 1 and text[1].isdigit():
        await _dm_resume(message, bot, mapping[cmd], int(text[1]))


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
