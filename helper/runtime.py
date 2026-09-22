from __future__ import annotations

import asyncio
import logging
from collections import defaultdict

from pyrogram import Client, filters
from pyrogram.types import Message

from .config import (
    ADDING_CHAT_ID,
    API_HASH,
    API_ID,
    HELPER_FORWARD_DELAY,
    HELPER_INLINE_TIMEOUT,
    HELPER_MAX_HISTORY,
    INLINE_OUTPUT_CHAT_ID,
    OWNER_IDS,
    SESSION_STRING,
    SOURCE_CHATS,
)

log = logging.getLogger("helper-userbot")


class HelperUserbot:
    """Safe source-channel forwarder + optional inline utility.

    Deliberately does NOT implement source-bot DM commands, crawlers, response
    watchers, or automatic /catch /grab /pick /hallow commands.
    """

    def __init__(self):
        self.client: Client | None = None
        self._started = False
        self._locks = defaultdict(asyncio.Lock)
        self._forwarded: set[tuple[str, int]] = set()

    def configured(self) -> bool:
        return bool(API_ID and API_HASH and SESSION_STRING and ADDING_CHAT_ID and SOURCE_CHATS)

    async def start(self) -> None:
        if self._started:
            return
        if not self.configured():
            log.warning("Helper userbot disabled: incomplete helper configuration")
            return

        self.client = Client(
            "adding_helper_forwarder",
            api_id=API_ID,
            api_hash=API_HASH,
            session_string=SESSION_STRING,
            in_memory=True,
            workdir="/tmp",
        )

        @self.client.on_message(filters.chat(list(SOURCE_CHATS)) & filters.media)
        async def source_media(_, message: Message):
            await self._forward_source_message(message)

        @self.client.on_message(filters.chat(list(SOURCE_CHATS)) & filters.caption)
        async def source_caption_only(_, message: Message):
            # Caption-only posts without media are never useful to Adding.
            return

        @self.client.on_message(filters.chat(ADDING_CHAT_ID) & filters.command(
            ["helperstatus", "helperforward", "helperstop", "helperinline"],
            prefixes="/",
        ))
        async def helper_control(_, message: Message):
            await self.control(message)

        await self.client.start()
        self._started = True
        log.info("Helper userbot started; source chats=%s", SOURCE_CHATS)

    async def stop(self) -> None:
        if self.client and self._started:
            await self.client.stop()
        self.client = None
        self._started = False

    async def _forward_source_message(self, message: Message) -> bool:
        if not self.client or not ADDING_CHAT_ID:
            return False

        chat = message.chat
        chat_key = str(getattr(chat, "id", "") or getattr(chat, "username", ""))
        key = (chat_key, int(message.id))
        if key in self._forwarded:
            return False

        async with self._locks[chat_key]:
            if key in self._forwarded:
                return False
            try:
                # Telegram-native forward: this preserves the source origin so
                # the Bot API ingest layer can verify the source safely.
                await message.forward(ADDING_CHAT_ID)
                self._forwarded.add(key)
                if len(self._forwarded) > 20000:
                    self._forwarded = set(list(self._forwarded)[-10000:])
                await asyncio.sleep(HELPER_FORWARD_DELAY)
                log.info("Forwarded source=%s message=%s -> adding=%s", chat_key, message.id, ADDING_CHAT_ID)
                return True
            except Exception:
                log.exception("Failed to forward source=%s message=%s", chat_key, message.id)
                return False

    async def forward_history(self, source_chat: str, limit: int = 100) -> int:
        """Owner-triggered backfill: only configured source chats are accepted."""
        if not self.client:
            raise RuntimeError("Helper userbot is not running")
        if source_chat not in SOURCE_CHATS:
            raise ValueError("source_chat is not in SOURCE_CHANNELS")
        limit = max(1, min(int(limit), HELPER_MAX_HISTORY))
        sent = 0
        async for message in self.client.get_chat_history(source_chat, limit=limit):
            if not message.media:
                continue
            if await self._forward_source_message(message):
                sent += 1
        return sent

    async def inline(self, bot_username: str, query: str) -> int:
        """Optional inline utility. It does not create Adding records directly."""
        if not self.client:
            raise RuntimeError("Helper userbot is not running")
        if not bot_username or not bot_username.startswith("@"):
            bot_username = "@" + bot_username.lstrip("@")
        results = await asyncio.wait_for(
            self.client.get_inline_bot_results(bot_username, query),
            timeout=HELPER_INLINE_TIMEOUT,
        )
        count = len(getattr(results, "results", []) or [])
        if count and INLINE_OUTPUT_CHAT_ID:
            await self.client.send_inline_bot_result(
                INLINE_OUTPUT_CHAT_ID,
                results.query_id,
                results.results[0].id,
                hide_via=True,
            )
        return count

    def is_owner(self, message: Message) -> bool:
        user = getattr(message, "from_user", None)
        return bool(user and int(user.id) in OWNER_IDS)

    async def control(self, message: Message) -> bool:
        """Handle only owner-issued helper controls in the configured Adding chat."""
        if not self.client or not self.is_owner(message):
            return False
        if int(getattr(message.chat, "id", 0) or 0) != ADDING_CHAT_ID:
            return False

        text = (message.text or "").strip()
        if not text:
            return False
        parts = text.split()
        cmd = parts[0].split("@", 1)[0].lower()

        if cmd == "/helperstatus":
            await message.reply_text(
                "Helper Userbot\n"
                "Mode: source-channel forward + inline utility\n"
                f"Sources: {len(SOURCE_CHATS)} configured\n"
                f"Adding: {ADDING_CHAT_ID}\n"
                "Source-bot DM/crawler: DISABLED"
            )
            return True

        if cmd == "/helperstop":
            await self.stop()
            await message.reply_text("Helper Userbot stopped.")
            return True

        if cmd == "/helperforward":
            if len(parts) < 2:
                await message.reply_text("Usage: /helperforward @source_channel [limit]")
                return True
            source = parts[1]
            limit = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else 100
            try:
                sent = await self.forward_history(source, limit)
                await message.reply_text(f"Forwarded: {sent}")
            except Exception as exc:
                await message.reply_text(f"Forward failed: {exc}")
            return True

        if cmd == "/helperinline":
            if len(parts) < 3:
                await message.reply_text("Usage: /helperinline @source_bot query")
                return True
            bot_username = parts[1]
            query = " ".join(parts[2:])
            try:
                count = await self.inline(bot_username, query)
                await message.reply_text(f"Inline results: {count}")
            except Exception as exc:
                await message.reply_text(f"Inline failed: {exc}")
            return True

        return False
