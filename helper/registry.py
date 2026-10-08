from __future__ import annotations

import re
import unicodedata
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from typing import Any

from parsers import PARSER_MAP
from unified.store import db

log_name = "helper-registry"
collection = db.helper_bots

MAX_PARSERS = 12

PARSER_ALIASES = {
    "capture": "capture_character",
    "character_catcher": "character_catcher_owo",
    "catcher": "character_catcher_owo",
    "generic": "generic_structured",
    "grab": "grab_family",
    "hallow": "hallow",
    "kairo": "kairo",
    "senpai": "senpai",
    "smash": "smash_character",
    "takers": "takers",
    "waifux": "waifux_global",
}
COMMAND_RE = re.compile(r"^/[A-Za-z0-9_]+$")
FIELD_RE = re.compile(r"^\s*([A-Za-z][A-Za-z0-9_ ]*)\s*[-:=]\s*(.*?)\s*$")
PARSER_FIELD_RE = re.compile(r"^parser\s*(\d+)$", re.I)


@dataclass(frozen=True, slots=True)
class AddedBotConfig:
    key: str
    bot: str
    command: str
    inline_source: str
    forward_source: str
    commands: tuple[str, ...]
    parsers: tuple[str, ...]
    created_at: str = ""
    updated_at: str = ""

    @property
    def inline_start_command(self) -> str | None:
        for command in self.commands:
            if command.startswith("/start") and not command.startswith("/startfw"):
                return command
        return None

    @property
    def inline_resume_command(self) -> str | None:
        for command in self.commands:
            if command.startswith("/resume") and not command.startswith("/resumefw"):
                return command
        return None

    @property
    def forward_start_command(self) -> str | None:
        for command in self.commands:
            if command.startswith("/startfw"):
                return command
        return None

    @property
    def forward_resume_command(self) -> str | None:
        for command in self.commands:
            if command.startswith("/resumefw"):
                return command
        return None


_CACHE: dict[str, AddedBotConfig] = {}


def _norm(value: Any) -> str:
    text = unicodedata.normalize("NFKC", str(value or ""))
    text = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", text)
    return text.strip().lower()


def _norm_source(value: Any) -> str:
    return _norm(value).lstrip("@")


def _slug(value: str) -> str:
    value = _norm_source(value)
    value = re.sub(r"[^a-z0-9_]+", "_", value).strip("_")
    return value or "bot"


def _command(value: str) -> str:
    value = _norm(value)
    if not value.startswith("/"):
        value = "/" + value
    return value.split("@", 1)[0]


def _split_csv(value: str) -> tuple[str, ...]:
    out: list[str] = []
    for item in re.split(r"[,|\n]+", value):
        item = item.strip()
        if item:
            out.append(item)
    return tuple(out)


def _build_config(
    *,
    bot: str,
    command: str,
    inline_source: str,
    forward_source: str,
    commands: tuple[str, ...],
    parsers: tuple[str, ...],
) -> AddedBotConfig:
    bot = "@" + _norm_source(bot)
    inline_source = _norm_source(inline_source)
    forward_source = _norm_source(forward_source)
    commands = tuple(dict.fromkeys(_command(x) for x in commands if str(x).strip()))
    parsers = tuple(dict.fromkeys(_norm(x) for x in parsers if str(x).strip()))
    now = datetime.now(timezone.utc).isoformat()
    return AddedBotConfig(
        key=f"items_{_slug(bot)}",
        bot=bot,
        command=_command(command),
        inline_source=inline_source,
        forward_source=forward_source,
        commands=commands,
        parsers=parsers,
        created_at=now,
        updated_at=now,
    )


def parse_addnewbot(text: str) -> AddedBotConfig:
    lines = [line.strip() for line in str(text or "").splitlines() if line.strip()]
    if not lines:
        raise ValueError("Empty /addnewbot payload")

    head = lines[0].split()
    if not head or head[0].split("@", 1)[0].lower() != "/addnewbot":
        raise ValueError("First line must be: /addnewbot @botusername")
    if len(head) < 2:
        raise ValueError("Missing bot username. Example: /addnewbot @newcardbot")

    values: dict[str, str] = {}
    parser_values: dict[int, str] = {}

    for line in lines[1:]:
        match = FIELD_RE.match(line)
        if not match:
            continue
        key = re.sub(r"\s+", " ", match.group(1).strip().lower())
        value = match.group(2).strip()
        parser_match = PARSER_FIELD_RE.match(key)
        if parser_match:
            parser_values[int(parser_match.group(1))] = value
        else:
            values[key] = value

    bot = head[1]
    command = values.get("cmd") or values.get("command")
    inline_source = values.get("inlinesource") or values.get("inline source") or bot
    forward_source = values.get("forwardsource") or values.get("forward source")
    commands = _split_csv(values.get("commands", ""))
    parsers = tuple(
        parser_values[index]
        for index in sorted(parser_values)
        if parser_values[index].strip()
    )

    if not re.match(r"^@[A-Za-z0-9_]{3,}$", bot):
        raise ValueError("Bot username must look like @newcardbot")
    if not command:
        raise ValueError("Missing cmd - /command")
    if not COMMAND_RE.match(_command(command)):
        raise ValueError("cmd must be a Telegram command such as /grab")
    if not inline_source:
        raise ValueError("Missing inlinesource - @botusername")
    if not forward_source:
        raise ValueError("Missing Forwardsource - @channel_or_chat_id")
    if not commands:
        raise ValueError("Missing commands - start,resume,startfw,resumefw")
    if len(commands) > 8:
        raise ValueError("At most 8 commands are allowed")
    if len(parsers) > MAX_PARSERS:
        raise ValueError(f"At most {MAX_PARSERS} parsers are allowed")
    if not parsers:
        parsers = ("generic",)

    canonical_parsers = tuple(PARSER_ALIASES.get(name, name) for name in parsers)
    unknown = [name for name in canonical_parsers if name not in PARSER_MAP]
    if unknown:
        available = ", ".join(PARSER_ALIASES)
        raise ValueError(
            f"Unknown parser(s): {', '.join(unknown)}. Available aliases: {available}"
        )

    normalized_commands = tuple(_command(item) for item in commands)
    if len(set(normalized_commands)) != len(normalized_commands):
        raise ValueError("commands contains duplicates")

    return _build_config(
        bot=bot,
        command=command,
        inline_source=inline_source,
        forward_source=forward_source,
        commands=normalized_commands,
        parsers=parsers,
    )


def all_configs() -> tuple[AddedBotConfig, ...]:
    return tuple(_CACHE.values())


def get_config(key: str | None) -> AddedBotConfig | None:
    return _CACHE.get(_norm(key))


def get_config_for_command(command: str | None) -> AddedBotConfig | None:
    command = _command(command or "")
    for config in _CACHE.values():
        if command in config.commands:
            return config
    return None


def parser_names_for_source(source_key: str | None) -> tuple[str, ...]:
    config = get_config(source_key)
    return tuple(PARSER_ALIASES.get(name, name) for name in config.parsers) if config else ()


def _matches_source(spec: str, values: set[str]) -> bool:
    if not spec:
        return False
    normalized = _norm_source(spec)
    return normalized in values


def match_config(
    *,
    username: str | None = None,
    user_id: int | str | None = None,
    chat_id: int | str | None = None,
    title: str | None = None,
    forward: bool = False,
) -> AddedBotConfig | None:
    username_value = _norm_source(username)
    user_values = {username_value} if username_value else set()
    if user_id is not None:
        user_values.add(_norm_source(user_id))

    chat_values = set()
    if chat_id is not None:
        chat_values.add(_norm_source(chat_id))
    if username:
        chat_values.add(_norm_source(username))
    if title:
        chat_values.add(_norm_source(title))

    for config in _CACHE.values():
        if forward:
            if _matches_source(config.forward_source, chat_values):
                return config
        elif _matches_source(config.inline_source, user_values):
            return config
    return None


async def ensure_registry_indexes() -> None:
    await collection.create_index("key", unique=True, name="uq_helper_bot_key")
    await collection.create_index("bot", unique=True, name="uq_helper_bot_username")


async def load_registry() -> int:
    _CACHE.clear()
    try:
        async for doc in collection.find({}):
            try:
                config = AddedBotConfig(
                    key=str(doc.get("key") or ""),
                    bot=str(doc.get("bot") or ""),
                    command=str(doc.get("command") or "/grab"),
                    inline_source=str(doc.get("inline_source") or ""),
                    forward_source=str(doc.get("forward_source") or ""),
                    commands=tuple(str(x) for x in (doc.get("commands") or [])),
                    parsers=tuple(str(x) for x in (doc.get("parsers") or [])),
                    created_at=str(doc.get("created_at") or ""),
                    updated_at=str(doc.get("updated_at") or ""),
                )
                if config.key and config.bot and config.commands:
                    _CACHE[config.key] = config
            except Exception:
                continue
    except Exception:
        return 0
    return len(_CACHE)


async def register_config(config: AddedBotConfig) -> AddedBotConfig:
    now = datetime.now(timezone.utc).isoformat()
    payload = {
        "key": config.key,
        "bot": config.bot,
        "command": config.command,
        "inline_source": config.inline_source,
        "forward_source": config.forward_source,
        "commands": list(config.commands),
        "parsers": list(config.parsers),
        "updated_at": now,
    }
    existing = await collection.find_one({"key": config.key}, {"created_at": 1})
    payload["created_at"] = str((existing or {}).get("created_at") or now)
    await collection.update_one(
        {"key": config.key},
        {"$set": payload},
        upsert=True,
    )
    saved = replace(config, created_at=payload["created_at"], updated_at=now)
    _CACHE[saved.key] = saved
    return saved
