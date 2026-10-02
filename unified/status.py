from __future__ import annotations

import time
from typing import Any

from aiogram.types import Message

from unified.config import settings
from unified.store import characters

PROCESS_STARTED_AT = time.time()


class RuntimeMetrics:
    def __init__(self) -> None:
        self.lookup_total = 0
        self.lookup_hits = 0
        self.lookup_misses = 0
        self.lookup_errors = 0
        self.lookup_ema_ms = 0.0
        self.ingest_total = 0
        self.ingest_saved = 0
        self.ingest_updated = 0

    def record_lookup(self, elapsed_ms: float, *, hit: bool, error: bool = False) -> None:
        self.lookup_total += 1
        if error:
            self.lookup_errors += 1
        elif hit:
            self.lookup_hits += 1
        else:
            self.lookup_misses += 1
        self.lookup_ema_ms = (
            elapsed_ms
            if self.lookup_ema_ms == 0
            else 0.15 * elapsed_ms + 0.85 * self.lookup_ema_ms
        )

    def record_ingest(self, status: str | None) -> None:
        self.ingest_total += 1
        value = str(status or "").lower()
        if value == "saved":
            self.ingest_saved += 1
        elif value == "updated":
            self.ingest_updated += 1

    def snapshot(self) -> dict[str, int | float]:
        return {
            "lookup_total": self.lookup_total,
            "lookup_hits": self.lookup_hits,
            "lookup_misses": self.lookup_misses,
            "lookup_errors": self.lookup_errors,
            "lookup_ema_ms": self.lookup_ema_ms,
            "ingest_total": self.ingest_total,
            "ingest_saved": self.ingest_saved,
            "ingest_updated": self.ingest_updated,
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
        data: dict[str, int] = {}
        with open("/proc/meminfo", "r", encoding="utf-8") as handle:
            for line in handle:
                parts = line.split()
                if len(parts) >= 2:
                    data[parts[0].rstrip(":")] = int(parts[1]) * 1024
        total = data.get("MemTotal", 0)
        available = data.get("MemAvailable", 0)
        used = max(total - available, 0)

        def fmt(value: int) -> str:
            return f"{value / (1024 ** 3):.2f} GB"

        return fmt(used), fmt(available), fmt(total)
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
    db_ping = await _ping_db()
    bot_ping = await _ping_bot(message)
    return (
        "🏓 <b>BIKA PING</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"🤖 Bot API : <code>{_fmt_ms(bot_ping)}</code>\n"
        f"🍃 MongoDB : <code>{_fmt_ms(db_ping)}</code>\n"
        f"⏱ Uptime : <code>{_uptime()}</code>\n"
        "━━━━━━━━━━━━━━━━━━"
    )


async def build_status_text(message: Message, *, helper_state: str, helper_text: str) -> str:
    count = await characters.count_documents({})
    sources = await characters.distinct("source_key")
    media_counts = {}
    for media_type in ("photo", "video", "animation", "document"):
        try:
            media_counts[media_type] = await characters.count_documents({"media_type": media_type})
        except Exception:
            media_counts[media_type] = 0

    db_ping = await _ping_db()
    snap = metrics.snapshot()
    lookup_state = "READY" if db_ping is not None else "DEGRADED"

    return (
        "♻ <b>ADDING & HELPER STATUS</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"‣ Service : <code>ONLINE</code>\n"
        f"‣ Database : <code>{settings.db_name}</code>\n"
        f"‣ MongoDB : <code>{lookup_state}</code>\n"
        f"‣ Adding Group : <code>{settings.adding_chat_id}</code>\n"
        f"‣ Total Media : <code>{_fmt_int(count)}</code>\n"
        f"‣ Sources : <code>{_fmt_int(len(sources))}</code>\n"
        f"‣ Photos : <code>{_fmt_int(media_counts['photo'])}</code>\n"
        f"‣ Videos : <code>{_fmt_int(media_counts['video'])}</code>\n"
        f"‣ GIF/Animation : <code>{_fmt_int(media_counts['animation'])}</code>\n\n"
        "⚡ <b>LOOKUP ENGINE</b>\n"
        f"‣ Exact UID : <code>ENABLED</code>\n"
        f"‣ Global UID Fallback : <code>{'ENABLED' if settings.v3_global_exact_fallback else 'DISABLED'}</code>\n"
        f"‣ Hash Fallback : <code>ENABLED</code>\n"
        f"‣ Lookup EMA : <code>{_fmt_ms(float(snap['lookup_ema_ms'])) if snap['lookup_total'] else 'N/A'}</code>\n"
        f"‣ Lookup Hits : <code>{_fmt_int(snap['lookup_hits'])}</code>\n"
        f"‣ Lookup Misses : <code>{_fmt_int(snap['lookup_misses'])}</code>\n\n"
        "🤖 <b>HELPER</b>\n"
        f"‣ Userbot : <code>{helper_state}</code>\n"
        f"{helper_text}\n\n"
        f"⏱ Uptime : <code>{_uptime()}</code>\n"
        "━━━━━━━━━━━━━━━━━━"
    )


async def build_stats_text(message: Message, *, helper_state: str) -> str:
    db_ping = await _ping_db()
    bot_ping = await _ping_bot(message)
    used, available, total = _ram_info()
    count = await characters.count_documents({})
    snap = metrics.snapshot()

    hit_rate = (
        (int(snap["lookup_hits"]) / int(snap["lookup_total"]) * 100)
        if int(snap["lookup_total"])
        else 0.0
    )

    return (
        "📊 <b>ADDING & LOOKUP STATS</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"‣ Uptime : <code>{_uptime()}</code>\n"
        f"‣ DB Ping : <code>{_fmt_ms(db_ping)}</code>\n"
        f"‣ Bot Ping : <code>{_fmt_ms(bot_ping)}</code>\n"
        f"‣ RAM Used : <code>{used}</code>\n"
        f"‣ RAM Available : <code>{available}</code>\n"
        f"‣ RAM Total : <code>{total}</code>\n\n"
        "⚡ <b>LOOKUP PERFORMANCE</b>\n"
        f"‣ Total Lookups : <code>{_fmt_int(snap['lookup_total'])}</code>\n"
        f"‣ Hits : <code>{_fmt_int(snap['lookup_hits'])}</code>\n"
        f"‣ Misses : <code>{_fmt_int(snap['lookup_misses'])}</code>\n"
        f"‣ Errors : <code>{_fmt_int(snap['lookup_errors'])}</code>\n"
        f"‣ Hit Rate : <code>{hit_rate:.1f}%</code>\n"
        f"‣ EMA Latency : <code>{_fmt_ms(float(snap['lookup_ema_ms'])) if snap['lookup_total'] else 'N/A'}</code>\n\n"
        "📥 <b>ADDING PERFORMANCE</b>\n"
        f"‣ Total Ingests : <code>{_fmt_int(snap['ingest_total'])}</code>\n"
        f"‣ New Records : <code>{_fmt_int(snap['ingest_saved'])}</code>\n"
        f"‣ Updated Records : <code>{_fmt_int(snap['ingest_updated'])}</code>\n\n"
        "🗄 <b>DATABASE</b>\n"
        f"‣ Characters : <code>{_fmt_int(count)}</code>\n"
        f"‣ DB : <code>{settings.db_name}</code>\n"
        f"‣ Helper : <code>{helper_state}</code>\n"
        "━━━━━━━━━━━━━━━━━━"
    )
