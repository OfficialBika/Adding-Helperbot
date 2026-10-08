from __future__ import annotations

import asyncio
import time
from typing import Any

from aiogram.types import Message

from unified.config import settings
from unified.store import characters

PROCESS_STARTED_AT = time.time()


class RuntimeMetrics:
    def __init__(self) -> None:
        self.ingest_total = 0
        self.ingest_saved = 0
        self.ingest_updated = 0
        self.ingest_skipped = 0

    def record_ingest(self, status: str | None) -> None:
        self.ingest_total += 1
        value = str(status or "").lower()
        if value == "saved":
            self.ingest_saved += 1
        elif value == "updated":
            self.ingest_updated += 1
        else:
            self.ingest_skipped += 1

    def snapshot(self) -> dict[str, int]:
        return {
            "ingest_total": self.ingest_total,
            "ingest_saved": self.ingest_saved,
            "ingest_updated": self.ingest_updated,
            "ingest_skipped": self.ingest_skipped,
        }


metrics = RuntimeMetrics()


def _fmt_int(value: Any) -> str:
    try:
        return f"{int(value):,}"
    except Exception:
        return "0"


def _fmt_ms(value: float | None) -> str:
    return "N/A" if value is None else f"{value:.0f} ms"


def _uptime() -> str:
    seconds = max(0, int(time.time() - PROCESS_STARTED_AT))
    days, seconds = divmod(seconds, 86400)
    hours, seconds = divmod(seconds, 3600)
    minutes, seconds = divmod(seconds, 60)
    if days:
        return f"{days}d {hours}h {minutes}m"
    if hours:
        return f"{hours}h {minutes}m {seconds}s"
    if minutes:
        return f"{minutes}m {seconds}s"
    return f"{seconds}s"


def _ram_info() -> tuple[str, str, str]:
    try:
        values: dict[str, int] = {}
        with open("/proc/meminfo", "r", encoding="utf-8") as handle:
            for line in handle:
                parts = line.split()
                if len(parts) >= 2:
                    values[parts[0].rstrip(":")] = int(parts[1]) * 1024
        total = values.get("MemTotal", 0)
        available = values.get("MemAvailable", 0)
        used = max(total - available, 0)
        return (
            f"{used / (1024 ** 3):.2f} GB",
            f"{available / (1024 ** 3):.2f} GB",
            f"{total / (1024 ** 3):.2f} GB",
        )
    except Exception:
        return "N/A", "N/A", "N/A"


async def _ping_db() -> float | None:
    try:
        started = time.perf_counter()
        await characters.database.command("ping")
        return (time.perf_counter() - started) * 1000
    except Exception:
        return None


async def _ping_bot(message: Message) -> float | None:
    try:
        started = time.perf_counter()
        await message.bot.get_me()
        return (time.perf_counter() - started) * 1000
    except Exception:
        return None


async def build_ping_text(message: Message) -> str:
    db_ping, bot_ping = await asyncio.gather(_ping_db(), _ping_bot(message))
    return (
        "🏓 <b>BIKA ADDING PING</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"🤖 Bot API : <code>{_fmt_ms(bot_ping)}</code>\n"
        f"🍃 MongoDB : <code>{_fmt_ms(db_ping)}</code>\n"
        f"⏱ Uptime : <code>{_uptime()}</code>\n"
        "━━━━━━━━━━━━━━━━━━"
    )


async def build_status_text(message: Message, *, helper_state: str) -> str:
    async def count(query: dict) -> int:
        try:
            return await characters.count_documents(query)
        except Exception:
            return 0

    async def sources() -> list[Any]:
        try:
            return await characters.distinct("source_key")
        except Exception:
            return []

    total, source_list, photos, videos, db_ping = await asyncio.gather(
        count({}),
        sources(),
        count({"media_type": "photo"}),
        count({"media_type": "video"}),
        _ping_db(),
    )
    return (
        "♻ <b>BIKA ADDING HELPER STATUS</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "‣ Service : <code>ONLINE</code>\n"
        f"‣ Database : <code>{settings.db_name}</code>\n"
        f"‣ MongoDB : <code>{'READY' if db_ping is not None else 'DEGRADED'}</code>\n"
        f"‣ Adding Group : <code>{settings.adding_chat_id}</code>\n"
        f"‣ Total Records : <code>{_fmt_int(total)}</code>\n"
        f"‣ Sources : <code>{_fmt_int(len(source_list))}</code>\n"
        f"‣ Photos : <code>{_fmt_int(photos)}</code>\n"
        f"‣ Videos : <code>{_fmt_int(videos)}</code>\n"
        f"‣ Helper : <code>{helper_state}</code>\n"
        f"⏱ Uptime : <code>{_uptime()}</code>\n"
        "━━━━━━━━━━━━━━━━━━"
    )


async def build_stats_text(message: Message, *, helper_state: str) -> str:
    try:
        total = await characters.count_documents({})
    except Exception:
        total = 0
    db_ping, bot_ping = await asyncio.gather(_ping_db(), _ping_bot(message))
    used, available, ram_total = _ram_info()
    snap = metrics.snapshot()
    return (
        "📊 <b>BIKA ADDING STATS</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"‣ Uptime : <code>{_uptime()}</code>\n"
        f"‣ DB Ping : <code>{_fmt_ms(db_ping)}</code>\n"
        f"‣ Bot Ping : <code>{_fmt_ms(bot_ping)}</code>\n"
        f"‣ RAM Used : <code>{used}</code>\n"
        f"‣ RAM Available : <code>{available}</code>\n"
        f"‣ RAM Total : <code>{ram_total}</code>\n\n"
        "📥 <b>ADDING PERFORMANCE</b>\n"
        f"‣ Total : <code>{_fmt_int(snap['ingest_total'])}</code>\n"
        f"‣ New Records : <code>{_fmt_int(snap['ingest_saved'])}</code>\n"
        f"‣ Updated Records : <code>{_fmt_int(snap['ingest_updated'])}</code>\n"
        f"‣ Skipped : <code>{_fmt_int(snap['ingest_skipped'])}</code>\n\n"
        "🗄 <b>DATABASE</b>\n"
        f"‣ Characters : <code>{_fmt_int(total)}</code>\n"
        f"‣ Helper : <code>{helper_state}</code>\n"
        "━━━━━━━━━━━━━━━━━━"
    )
