from __future__ import annotations

import asyncio
import logging
import time
import uuid
from collections import OrderedDict
from datetime import datetime, timedelta, timezone
from typing import Any

import aiohttp
from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
from aiogram.exceptions import (
    TelegramBadRequest,
    TelegramForbiddenError,
    TelegramNetworkError,
    TelegramRetryAfter,
)
from aiogram.filters import Command, CommandObject
from aiogram.types import (
    CallbackQuery,
    Chat,
    ChatMemberUpdated,
    ErrorEvent,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
    Update,
)
from pymongo import ReturnDocument, UpdateOne

from unified.config import settings
from unified.store import db

log = logging.getLogger("unified.broadcast")

broadcast_router = Router(name="production-broadcast")

ACTIVE_CHAT_TYPES = frozenset({"private", "group", "supergroup"})
GROUP_CHAT_TYPES = frozenset({"group", "supergroup"})
BROADCAST_CONFIRM_TTL = timedelta(minutes=15)
BROADCAST_MAX_ATTEMPTS = 4
BROADCAST_CONCURRENCY = 4
BROADCAST_RATE_PER_SECOND = 18.0
BROADCAST_DELIVERY_BATCH_SIZE = 400
CHAT_REGISTRY_TOUCH_SECONDS = 600.0
CHAT_REGISTRY_MAX_MEMORY_ENTRIES = 50_000
PROGRESS_UPDATE_EVERY = 25

bot_chats = db.bot_chats
broadcast_jobs = db.broadcast_jobs
broadcast_deliveries = db.broadcast_deliveries

_wakeup = asyncio.Event()
_worker_task: asyncio.Task | None = None
_cancel_events: dict[str, asyncio.Event] = {}
_progress_locks: dict[str, asyncio.Lock] = {}


def _now() -> datetime:
    return datetime.now(timezone.utc)


def _enum_value(value: Any) -> str:
    return str(getattr(value, "value", value) or "").lower()


def is_broadcast_chat_type(chat_type: Any) -> bool:
    """Return whether a Telegram private chat or group is a broadcast target."""
    return _enum_value(chat_type) in ACTIVE_CHAT_TYPES


def is_send_permission_error(exc: BaseException | str) -> bool:
    """Match Telegram's known write-permission errors, not arbitrary API failures."""
    text = str(exc).lower()
    return any(
        marker in text
        for marker in (
            "not enough rights to send text messages",
            "not enough rights to send messages",
            "chat_write_forbidden",
            "have no rights to send messages",
            "bot can't send messages to this chat",
            "bots can't send messages in this chat",
        )
    )


def _event_chat(update: Update | Any) -> Chat | None:
    for attr in (
        "message",
        "edited_message",
        "channel_post",
        "edited_channel_post",
    ):
        message = getattr(update, attr, None)
        chat = getattr(message, "chat", None) if message is not None else None
        if chat is not None:
            return chat

    callback = getattr(update, "callback_query", None)
    callback_message = getattr(callback, "message", None) if callback is not None else None
    chat = getattr(callback_message, "chat", None) if callback_message is not None else None
    if chat is not None:
        return chat

    membership = getattr(update, "my_chat_member", None)
    if membership is not None:
        return getattr(membership, "chat", None)
    return None


def _membership_state(event: ChatMemberUpdated) -> str | None:
    status = _enum_value(getattr(event.new_chat_member, "status", None))
    is_member = getattr(event.new_chat_member, "is_member", None)
    if status in {"left", "kicked"} or (status == "restricted" and is_member is False):
        return "inactive"
    if status in {"member", "administrator", "creator"} or (
        status == "restricted" and is_member is True
    ):
        return "active"
    return None


async def _record_chat(chat: Chat, *, status: str | None = None) -> None:
    chat_type = _enum_value(getattr(chat, "type", None))
    if chat_type not in ACTIVE_CHAT_TYPES:
        return

    now = _now()
    values: dict[str, Any] = {
        "chat_type": chat_type,
        "title": str(getattr(chat, "title", None) or "")[:256],
        "username": str(getattr(chat, "username", None) or "")[:64],
        "last_seen_at": now,
    }
    if status:
        values["status"] = status

    update: dict[str, Any] = {"$set": values}
    if status is None:
        update["$setOnInsert"] = {"status": "active", "first_seen_at": now}
    else:
        update["$setOnInsert"] = {"first_seen_at": now}

    await bot_chats.update_one({"chat_id": int(chat.id)}, update, upsert=True)


class ChatRegistryMiddleware(BaseMiddleware):
    """Register reachable chats with bounded in-memory write coalescing."""

    def __init__(self) -> None:
        self._last_touched: OrderedDict[int, float] = OrderedDict()

    async def __call__(self, handler, event: Update, data: dict[str, Any]):
        try:
            membership = getattr(event, "my_chat_member", None)
            if membership is not None:
                chat = getattr(membership, "chat", None)
                if chat is not None and _enum_value(getattr(chat, "type", None)) in GROUP_CHAT_TYPES:
                    await _record_chat(chat, status=_membership_state(membership))
            else:
                chat = _event_chat(event)
                if chat is not None and is_broadcast_chat_type(getattr(chat, "type", None)):
                    chat_id = int(chat.id)
                    now = time.monotonic()
                    last = self._last_touched.get(chat_id)
                    if last is None or now - last >= CHAT_REGISTRY_TOUCH_SECONDS:
                        # Only throttle after a successful write; transient DB errors
                        # should not make this chat invisible for the full TTL.
                        await _record_chat(chat)
                        self._last_touched[chat_id] = now
                    else:
                        self._last_touched[chat_id] = last
                    self._last_touched.move_to_end(chat_id)
                    while len(self._last_touched) > CHAT_REGISTRY_MAX_MEMORY_ENTRIES:
                        self._last_touched.popitem(last=False)
        except asyncio.CancelledError:
            raise
        except Exception:
            # Chat discovery is auxiliary and must never block bot updates.
            log.exception("CHAT REGISTRY update failed")
        return await handler(event, data)


async def initialize_broadcast() -> None:
    """Create isolated broadcast indexes and recover interrupted jobs safely."""
    await bot_chats.create_index("chat_id", unique=True, name="uq_bot_chats_chat_id")
    await broadcast_jobs.create_index(
        [("status", 1), ("created_at", 1)],
        name="idx_broadcast_jobs_status_created",
    )
    await broadcast_jobs.create_index("job_id", unique=True, name="uq_broadcast_jobs_job_id")
    await broadcast_deliveries.create_index(
        [("job_id", 1), ("chat_id", 1)],
        unique=True,
        name="uq_broadcast_delivery_job_chat",
    )
    await broadcast_deliveries.create_index(
        [("job_id", 1), ("status", 1), ("_id", 1)],
        name="idx_broadcast_delivery_pending",
    )

    now = _now()
    await broadcast_jobs.update_many(
        {"status": "pending_confirmation", "expires_at": {"$lte": now}},
        {"$set": {"status": "expired", "updated_at": now}},
    )
    active_job_ids = [
        doc["job_id"]
        async for doc in broadcast_jobs.find(
            {"status": {"$in": ["queued", "running"]}},
            {"_id": 0, "job_id": 1},
        )
        if doc.get("job_id")
    ]
    if active_job_ids:
        await broadcast_deliveries.update_many(
            {"job_id": {"$in": active_job_ids}, "status": "sending"},
            {"$set": {"status": "pending", "recovered_at": now}},
        )
    await broadcast_jobs.update_many(
        {"status": "running"},
        {"$set": {"status": "queued", "resumed_at": now, "updated_at": now}},
    )


async def auto_leave_restricted_group(bot: Bot, chat: Chat, exc: BaseException | str) -> bool:
    """Leave only a group where Telegram explicitly denies message-send rights."""
    chat_type = _enum_value(getattr(chat, "type", None))
    if chat_type not in GROUP_CHAT_TYPES or not is_send_permission_error(exc):
        return False

    chat_id = int(chat.id)
    now = _now()
    try:
        left = await bot.leave_chat(chat_id=chat_id)
        state = "left_send_permission" if left else "inactive_send_permission"
        await bot_chats.update_one(
            {"chat_id": chat_id},
            {
                "$set": {
                    "chat_type": chat_type,
                    "status": state,
                    "left_at": now,
                    "send_permission_error": str(exc)[:500],
                    "last_seen_at": now,
                },
                "$setOnInsert": {
                    "first_seen_at": now,
                    "title": str(getattr(chat, "title", None) or "")[:256],
                    "username": str(getattr(chat, "username", None) or "")[:64],
                },
            },
            upsert=True,
        )
        log.warning(
            "AUTO LEAVE group=%s title=%r result=%s reason=send_permission_denied",
            chat_id,
            getattr(chat, "title", None),
            left,
        )
        return True
    except asyncio.CancelledError:
        raise
    except Exception:
        log.exception(
            "AUTO LEAVE failed group=%s title=%r after Telegram send-permission denial",
            chat_id,
            getattr(chat, "title", None),
        )
        try:
            await bot_chats.update_one(
                {"chat_id": chat_id},
                {
                    "$set": {
                        "chat_type": chat_type,
                        "status": "leave_failed_send_permission",
                        "left_attempt_at": now,
                        "send_permission_error": str(exc)[:500],
                    },
                    "$setOnInsert": {
                        "first_seen_at": now,
                        "title": str(getattr(chat, "title", None) or "")[:256],
                        "username": str(getattr(chat, "username", None) or "")[:64],
                    },
                },
                upsert=True,
            )
        except Exception:
            log.exception("AUTO LEAVE status persistence failed group=%s", chat_id)
        return True


async def _handle_dispatch_error(event: ErrorEvent, bot: Bot) -> bool:
    """Handle only send-right errors in groups; let unrelated errors propagate."""
    exc = event.exception
    if not is_send_permission_error(exc):
        return False
    chat = _event_chat(event.update)
    if chat is None or _enum_value(getattr(chat, "type", None)) not in GROUP_CHAT_TYPES:
        return False
    await auto_leave_restricted_group(bot, chat, exc)
    return True


def _target_query() -> dict[str, Any]:
    return {
        "status": "active",
        "chat_type": {"$in": sorted(ACTIVE_CHAT_TYPES)},
        "chat_id": {"$nin": [int(value) for value in settings.owner_ids]},
    }


def _format_progress(job: dict[str, Any]) -> str:
    status = str(job.get("status") or "unknown")
    sent = int(job.get("sent_count") or 0)
    failed = int(job.get("failed_count") or 0)
    completed = int(job.get("completed_count") or sent + failed)
    targets = int(job.get("target_count") or 0)
    return (
        "📣 <b>Broadcast</b>\n\n"
        f"Job: <code>{job.get('job_id', '—')}</code>\n"
        f"Status: <b>{status.replace('_', ' ').upper()}</b>\n"
        f"Progress: <code>{completed}/{targets}</code>\n"
        f"✅ Sent: <code>{sent}</code>\n"
        f"⚠️ Failed: <code>{failed}</code>\n"
        f"⏭ Skipped: <code>{int(job.get('skipped_count') or 0)}</code>"
    )


async def _edit_control_message(bot: Bot, job: dict[str, Any]) -> None:
    chat_id = job.get("control_chat_id")
    message_id = job.get("control_message_id")
    if not chat_id or not message_id:
        return
    lock = _progress_locks.setdefault(str(job.get("job_id")), asyncio.Lock())
    async with lock:
        try:
            latest = await broadcast_jobs.find_one({"job_id": job.get("job_id")}, {"_id": 0})
            if not latest:
                return
            await bot.edit_message_text(
                chat_id=int(chat_id),
                message_id=int(message_id),
                text=_format_progress(latest),
                parse_mode="HTML",
                reply_markup=None,
            )
        except TelegramBadRequest as exc:
            if "message is not modified" not in str(exc).lower():
                log.warning("BROADCAST progress edit failed job=%s error=%s", job.get("job_id"), exc)
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("BROADCAST progress edit failed job=%s", job.get("job_id"))


class _RateLimiter:
    """A shared pacing gate across concurrent broadcast workers."""

    def __init__(self, rate_per_second: float) -> None:
        self._interval = 1.0 / max(rate_per_second, 1.0)
        self._next_at = 0.0
        self._lock = asyncio.Lock()

    async def wait(self) -> None:
        async with self._lock:
            now = time.monotonic()
            slot = max(now, self._next_at)
            self._next_at = slot + self._interval
            delay = slot - now
        if delay > 0:
            await asyncio.sleep(delay)


_rate_limiter = _RateLimiter(BROADCAST_RATE_PER_SECOND)


async def _mark_chat_unreachable(chat_id: int, reason: str) -> None:
    try:
        await bot_chats.update_one(
            {"chat_id": int(chat_id)},
            {
                "$set": {
                    "status": "inactive_unreachable",
                    "inactive_reason": reason[:500],
                    "last_delivery_failure_at": _now(),
                }
            },
        )
    except Exception:
        log.exception("BROADCAST could not mark chat inactive chat=%s", chat_id)


async def _deliver_to_chat(bot: Bot, job: dict[str, Any], delivery: dict[str, Any]) -> tuple[bool, str]:
    chat_id = int(delivery["chat_id"])
    chat_type = str(delivery.get("chat_type") or "")
    last_error = "Unknown error"

    for attempt in range(1, BROADCAST_MAX_ATTEMPTS + 1):
        await _rate_limiter.wait()
        try:
            if job.get("payload_type") == "copy":
                await bot.copy_message(
                    chat_id=chat_id,
                    from_chat_id=int(job["source_chat_id"]),
                    message_id=int(job["source_message_id"]),
                )
            else:
                await bot.send_message(
                    chat_id=chat_id,
                    text=str(job.get("text") or ""),
                    parse_mode=None,
                )
            return True, ""
        except TelegramRetryAfter as exc:
            last_error = f"rate limited; retry_after={exc.retry_after}s"
            if attempt >= BROADCAST_MAX_ATTEMPTS:
                break
            await asyncio.sleep(max(float(exc.retry_after), 1.0))
        except (TelegramNetworkError, aiohttp.ClientError, TimeoutError, OSError) as exc:
            last_error = f"{type(exc).__name__}: {exc}"
            if attempt >= BROADCAST_MAX_ATTEMPTS:
                break
            await asyncio.sleep(min(2 ** (attempt - 1), 8))
        except (TelegramBadRequest, TelegramForbiddenError) as exc:
            last_error = f"{type(exc).__name__}: {exc}"
            if is_send_permission_error(exc) and chat_type in GROUP_CHAT_TYPES:
                record = await bot_chats.find_one({"chat_id": chat_id}, {"title": 1, "username": 1})
                chat = Chat(
                    id=chat_id,
                    type=chat_type,
                    title=str((record or {}).get("title") or "") or None,
                    username=str((record or {}).get("username") or "") or None,
                )
                await auto_leave_restricted_group(bot, chat, exc)
            elif any(
                marker in str(exc).lower()
                for marker in ("bot was blocked by the user", "user is deactivated", "chat not found")
            ):
                await _mark_chat_unreachable(chat_id, str(exc))
            elif "bot was kicked" in str(exc).lower() and chat_type in GROUP_CHAT_TYPES:
                await _mark_chat_unreachable(chat_id, str(exc))
            return False, last_error
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            last_error = f"{type(exc).__name__}: {exc}"
            log.exception("BROADCAST delivery unexpectedly failed job=%s chat=%s", job.get("job_id"), chat_id)
            return False, last_error

    return False, last_error


async def _initialize_job_deliveries(job: dict[str, Any]) -> int:
    job_id = str(job["job_id"])
    existing = await broadcast_jobs.find_one(
        {"job_id": job_id},
        {"_id": 0, "targets_initialized": 1, "target_count": 1},
    )
    if existing and existing.get("targets_initialized"):
        return int(existing.get("target_count") or 0)

    batch: list[UpdateOne] = []
    cursor = bot_chats.find(
        _target_query(),
        {"_id": 0, "chat_id": 1, "chat_type": 1},
    ).sort("chat_id", 1)
    async for recipient in cursor:
        chat_id = recipient.get("chat_id")
        if not isinstance(chat_id, int):
            continue
        batch.append(
            UpdateOne(
                {"job_id": job_id, "chat_id": int(chat_id)},
                {
                    "$setOnInsert": {
                        "job_id": job_id,
                        "chat_id": int(chat_id),
                        "chat_type": str(recipient.get("chat_type") or ""),
                        "status": "pending",
                        "attempts": 0,
                        "created_at": _now(),
                    }
                },
                upsert=True,
            )
        )
        if len(batch) >= BROADCAST_DELIVERY_BATCH_SIZE:
            await broadcast_deliveries.bulk_write(batch, ordered=False)
            batch.clear()
    if batch:
        await broadcast_deliveries.bulk_write(batch, ordered=False)

    target_count = await broadcast_deliveries.count_documents({"job_id": job_id})
    await broadcast_jobs.update_one(
        {"job_id": job_id},
        {"$set": {"targets_initialized": True, "target_count": target_count, "updated_at": _now()}},
    )
    log.info("BROADCAST targets initialized job=%s targets=%s", job_id, target_count)
    return target_count


async def _record_delivery_result(
    bot: Bot,
    job_id: str,
    delivery_id: Any,
    *,
    sent: bool,
    error: str = "",
) -> None:
    now = _now()
    status = "sent" if sent else "failed"
    await broadcast_deliveries.update_one(
        {"_id": delivery_id, "job_id": job_id},
        {
            "$set": {
                "status": status,
                "sent_at": now if sent else None,
                "last_error": error[:1000],
                "updated_at": now,
            }
        },
    )
    increments: dict[str, int] = {"completed_count": 1}
    increments["sent_count" if sent else "failed_count"] = 1
    updated = await broadcast_jobs.find_one_and_update(
        {"job_id": job_id},
        {"$inc": increments, "$set": {"updated_at": now}},
        return_document=ReturnDocument.AFTER,
    )
    if updated:
        completed = int(updated.get("completed_count") or 0)
        if completed and completed % PROGRESS_UPDATE_EVERY == 0:
            await _edit_control_message(bot, updated)


async def _delivery_worker(bot: Bot, job: dict[str, Any], cancel_event: asyncio.Event) -> None:
    job_id = str(job["job_id"])
    while not cancel_event.is_set():
        delivery = await broadcast_deliveries.find_one_and_update(
            {"job_id": job_id, "status": "pending"},
            {
                "$set": {"status": "sending", "attempted_at": _now()},
                "$inc": {"attempts": 1},
            },
            sort=[("_id", 1)],
            return_document=ReturnDocument.AFTER,
        )
        if not delivery:
            return
        sent, error = await _deliver_to_chat(bot, job, delivery)
        await _record_delivery_result(bot, job_id, delivery["_id"], sent=sent, error=error)


async def _reconcile_job_counts(job_id: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    async for row in broadcast_deliveries.aggregate([
        {"$match": {"job_id": job_id}},
        {"$group": {"_id": "$status", "count": {"$sum": 1}}},
    ]):
        counts[str(row.get("_id") or "")] = int(row.get("count") or 0)

    target_count = sum(counts.values())
    sent_count = counts.get("sent", 0)
    failed_count = counts.get("failed", 0)
    skipped_count = counts.get("skipped", 0)
    completed_count = sent_count + failed_count
    await broadcast_jobs.update_one(
        {"job_id": job_id},
        {
            "$set": {
                "target_count": target_count,
                "sent_count": sent_count,
                "failed_count": failed_count,
                "skipped_count": skipped_count,
                "completed_count": completed_count,
                "updated_at": _now(),
            }
        },
    )
    return {
        "target_count": target_count,
        "sent_count": sent_count,
        "failed_count": failed_count,
        "skipped_count": skipped_count,
        "completed_count": completed_count,
        "pending_count": counts.get("pending", 0),
        "sending_count": counts.get("sending", 0),
    }


async def _process_job(bot: Bot, job: dict[str, Any]) -> None:
    job_id = str(job["job_id"])
    cancel_event = _cancel_events.setdefault(job_id, asyncio.Event())
    current = await broadcast_jobs.find_one({"job_id": job_id}, {"_id": 0})
    if current and current.get("cancel_requested"):
        cancel_event.set()

    targets = await _initialize_job_deliveries(job)
    await broadcast_jobs.update_one(
        {"job_id": job_id},
        {"$set": {"target_count": targets, "updated_at": _now()}},
    )
    await _edit_control_message(bot, {"job_id": job_id, **(current or job)})

    if targets == 0:
        await broadcast_jobs.update_one(
            {"job_id": job_id},
            {"$set": {"status": "completed", "completed_at": _now(), "updated_at": _now()}},
        )
        final_job = await broadcast_jobs.find_one({"job_id": job_id}, {"_id": 0})
        if final_job:
            await _edit_control_message(bot, final_job)
        _cancel_events.pop(job_id, None)
        _progress_locks.pop(job_id, None)
        return

    workers = [
        asyncio.create_task(
            _delivery_worker(bot, job, cancel_event),
            name=f"broadcast-{job_id[:8]}-{index}",
        )
        for index in range(BROADCAST_CONCURRENCY)
    ]
    try:
        await asyncio.gather(*workers)
    finally:
        for task in workers:
            if not task.done():
                task.cancel()
        await asyncio.gather(*workers, return_exceptions=True)

    if cancel_event.is_set():
        await broadcast_deliveries.update_many(
            {"job_id": job_id, "status": {"$in": ["pending", "sending"]}},
            {"$set": {"status": "skipped", "updated_at": _now(), "last_error": "Cancelled by owner"}},
        )
        final_status = "cancelled"
    else:
        counts = await _reconcile_job_counts(job_id)
        if counts["pending_count"] or counts["sending_count"]:
            # Never label a job complete while any recipient has no terminal result.
            await broadcast_jobs.update_one(
                {"job_id": job_id},
                {"$set": {"status": "queued", "updated_at": _now()}},
            )
            _wakeup.set()
            return
        final_status = "completed_with_errors" if counts["failed_count"] else "completed"

    await broadcast_jobs.update_one(
        {"job_id": job_id},
        {"$set": {"status": final_status, "completed_at": _now(), "updated_at": _now()}},
    )
    final_job = await broadcast_jobs.find_one({"job_id": job_id}, {"_id": 0})
    log.info(
        "BROADCAST finished job=%s status=%s targets=%s sent=%s failed=%s skipped=%s",
        job_id,
        final_status,
        (final_job or {}).get("target_count", 0),
        (final_job or {}).get("sent_count", 0),
        (final_job or {}).get("failed_count", 0),
        (final_job or {}).get("skipped_count", 0),
    )
    if final_job:
        await _edit_control_message(bot, final_job)
    _cancel_events.pop(job_id, None)
    _progress_locks.pop(job_id, None)


async def _worker_loop(bot: Bot) -> None:
    while True:
        await _wakeup.wait()
        _wakeup.clear()
        while True:
            try:
                job = await broadcast_jobs.find_one_and_update(
                    {"status": "queued"},
                    {"$set": {"status": "running", "started_at": _now(), "updated_at": _now()}},
                    sort=[("created_at", 1)],
                    return_document=ReturnDocument.AFTER,
                )
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("BROADCAST worker could not claim a queued job")
                await asyncio.sleep(5)
                _wakeup.set()
                break
            if not job:
                break
            try:
                await _process_job(bot, job)
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("BROADCAST worker failed job=%s; keeping job recoverable", job.get("job_id"))
                await broadcast_deliveries.update_many(
                    {"job_id": job.get("job_id"), "status": "sending"},
                    {"$set": {"status": "pending", "recovered_at": _now()}},
                )
                await broadcast_jobs.update_one(
                    {"job_id": job.get("job_id")},
                    {
                        "$set": {
                            "status": "queued",
                            "worker_error_at": _now(),
                            "updated_at": _now(),
                        }
                    },
                )
                await asyncio.sleep(5)
                _wakeup.set()
                break


def start_broadcast_worker(bot: Bot) -> None:
    global _worker_task
    if _worker_task is not None and not _worker_task.done():
        return
    _worker_task = asyncio.create_task(_worker_loop(bot), name="broadcast-worker")
    _wakeup.set()


async def stop_broadcast_worker() -> None:
    global _worker_task
    task = _worker_task
    _worker_task = None
    if task is None:
        return
    task.cancel()
    try:
        await task
    except asyncio.CancelledError:
        pass


async def _stage_broadcast(message: Message, command: CommandObject) -> None:
    if not message.from_user or message.from_user.id not in settings.owner_ids:
        return
    if _enum_value(message.chat.type) != "private":
        await message.reply("For safety, use /broadcast in the bot's private chat.")
        return

    args = str(command.args or "").strip()
    if args.lower() in {"status", "cancel"}:
        if args.lower() == "status":
            await _send_broadcast_status(message)
        else:
            await _cancel_latest_broadcast(message)
        return

    replied = getattr(message, "reply_to_message", None)
    if args:
        if len(args) > 4096:
            await message.reply("❌ Text broadcasts must be 4096 characters or fewer. Reply to a message to copy media or longer content.")
            return
        payload_type = "text"
        payload = {"text": args}
    elif replied is not None:
        payload_type = "copy"
        payload = {"source_chat_id": int(replied.chat.id), "source_message_id": int(replied.message_id)}
    else:
        await message.reply(
            "Usage:\n"
            "• Send <code>/broadcast Your announcement</code> for plain text.\n"
            "• Reply to a message with <code>/broadcast</code> to copy text or media.\n"
            "• <code>/broadcast status</code> to view recent jobs.\n"
            "• <code>/broadcast cancel</code> to cancel the latest active job."
        )
        return

    recipients = await bot_chats.count_documents(_target_query())
    if recipients <= 0:
        await message.reply("No active broadcast recipients are registered yet.")
        return

    job_id = uuid.uuid4().hex
    now = _now()
    job = {
        "job_id": job_id,
        "creator_id": int(message.from_user.id),
        "status": "pending_confirmation",
        "payload_type": payload_type,
        **payload,
        "created_at": now,
        "updated_at": now,
        "expires_at": now + BROADCAST_CONFIRM_TTL,
        "target_count": 0,
        "sent_count": 0,
        "failed_count": 0,
        "completed_count": 0,
        "skipped_count": 0,
        "targets_initialized": False,
        "cancel_requested": False,
    }
    await broadcast_jobs.insert_one(job)

    preview_text = (
        "⚠️ <b>Confirm broadcast</b>\n\n"
        f"Current eligible destinations: <code>{recipients}</code>\n"
        f"Payload: <code>{'text' if payload_type == 'text' else 'copied message/media'}</code>\n"
        "Recipients are active chats the bot has seen or groups where it is a member. "
        "Private chats opted out of broadcasts are excluded.\n\n"
        "This action sends to every eligible destination. Confirm within 15 minutes."
    )
    keyboard = InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="✅ Confirm", callback_data=f"bc:confirm:{job_id}"),
                InlineKeyboardButton(text="✖ Cancel", callback_data=f"bc:cancel:{job_id}"),
            ]
        ]
    )
    try:
        preview = await message.reply(preview_text, reply_markup=keyboard)
        await broadcast_jobs.update_one(
            {"job_id": job_id},
            {
                "$set": {
                    "control_chat_id": int(preview.chat.id),
                    "control_message_id": int(preview.message_id),
                    "updated_at": _now(),
                }
            },
        )
    except Exception:
        await broadcast_jobs.update_one(
            {"job_id": job_id},
            {"$set": {"status": "failed_preview", "updated_at": _now()}},
        )
        raise


async def _send_broadcast_status(message: Message) -> None:
    jobs = [
        job
        async for job in broadcast_jobs.find(
            {"creator_id": int(message.from_user.id)},
            {"_id": 0},
        ).sort("created_at", -1).limit(5)
    ]
    if not jobs:
        await message.reply("No broadcast jobs found.")
        return
    lines = ["📣 <b>Recent broadcasts</b>", ""]
    for job in jobs:
        lines.append(
            f"• <code>{job.get('job_id', '—')[:8]}</code> "
            f"<b>{str(job.get('status', 'unknown')).replace('_', ' ').upper()}</b> — "
            f"{int(job.get('sent_count') or 0)} sent, "
            f"{int(job.get('failed_count') or 0)} failed, "
            f"{int(job.get('target_count') or 0)} targets"
        )
    await message.reply("\n".join(lines))


async def _cancel_latest_broadcast(message: Message) -> None:
    query = {
        "creator_id": int(message.from_user.id),
        "status": {"$in": ["pending_confirmation", "queued", "running"]},
    }
    job = await broadcast_jobs.find_one(query, sort=[("created_at", -1)])
    if not job:
        await message.reply("No active broadcast job to cancel.")
        return

    job_id = str(job["job_id"])
    if job.get("status") == "running":
        await broadcast_jobs.update_one(
            {"job_id": job_id, "status": "running"},
            {"$set": {"cancel_requested": True, "updated_at": _now()}},
        )
        _cancel_events.setdefault(job_id, asyncio.Event()).set()
        await message.reply(f"Cancellation requested for <code>{job_id[:8]}</code>.")
    else:
        await broadcast_jobs.update_one(
            {"job_id": job_id, "status": {"$in": ["pending_confirmation", "queued"]}},
            {"$set": {"status": "cancelled", "completed_at": _now(), "updated_at": _now()}},
        )
        await message.reply(f"Broadcast <code>{job_id[:8]}</code> cancelled.")


@broadcast_router.message(Command("broadcast"))
async def broadcast_command(message: Message, command: CommandObject) -> None:
    await _stage_broadcast(message, command)


@broadcast_router.message(Command("stopbroadcast"))
async def stopbroadcast_command(message: Message) -> None:
    if not message.from_user or _enum_value(message.chat.type) != "private":
        return
    await bot_chats.update_one(
        {"chat_id": int(message.chat.id)},
        {
            "$set": {
                "chat_type": "private",
                "status": "opted_out",
                "opted_out_at": _now(),
                "last_seen_at": _now(),
            },
            "$setOnInsert": {"first_seen_at": _now(), "title": "", "username": ""},
        },
        upsert=True,
    )
    await message.reply("✅ You have opted out of bot broadcasts. Use /startbroadcast to opt back in.")


@broadcast_router.message(Command("startbroadcast"))
async def startbroadcast_command(message: Message) -> None:
    if not message.from_user or _enum_value(message.chat.type) != "private":
        return
    await bot_chats.update_one(
        {"chat_id": int(message.chat.id)},
        {
            "$set": {
                "chat_type": "private",
                "status": "active",
                "opted_in_at": _now(),
                "last_seen_at": _now(),
            },
            "$setOnInsert": {"first_seen_at": _now(), "title": "", "username": ""},
        },
        upsert=True,
    )
    await message.reply("✅ You have opted in to bot broadcasts again.")


@broadcast_router.callback_query(F.data.startswith("bc:"))
async def broadcast_confirmation_callback(query: CallbackQuery) -> None:
    if not query.from_user or query.from_user.id not in settings.owner_ids:
        await query.answer("Not authorized.", show_alert=True)
        return

    parts = str(query.data or "").split(":")
    if len(parts) != 3 or parts[1] not in {"confirm", "cancel"}:
        await query.answer("Invalid broadcast action.", show_alert=True)
        return
    action, job_id = parts[1], parts[2]
    job = await broadcast_jobs.find_one(
        {"job_id": job_id, "creator_id": int(query.from_user.id)},
        {"_id": 0},
    )
    if not job:
        await query.answer("Broadcast job was not found.", show_alert=True)
        return
    if job.get("status") != "pending_confirmation":
        await query.answer(f"Already {str(job.get('status') or 'handled').replace('_', ' ')}.", show_alert=True)
        return
    if job.get("expires_at") and job["expires_at"] <= _now():
        await broadcast_jobs.update_one(
            {"job_id": job_id, "status": "pending_confirmation"},
            {"$set": {"status": "expired", "updated_at": _now()}},
        )
        await query.answer("Confirmation expired. Create a new broadcast.", show_alert=True)
        try:
            if query.message:
                await query.message.edit_text("⌛ Broadcast confirmation expired.")
        except Exception:
            log.exception("BROADCAST expiry message edit failed job=%s", job_id)
        return

    if action == "cancel":
        await broadcast_jobs.update_one(
            {"job_id": job_id, "status": "pending_confirmation"},
            {"$set": {"status": "cancelled", "completed_at": _now(), "updated_at": _now()}},
        )
        await query.answer("Broadcast cancelled.")
        try:
            if query.message:
                await query.message.edit_text("✖ Broadcast cancelled.")
        except Exception:
            log.exception("BROADCAST cancel message edit failed job=%s", job_id)
        return

    updated = await broadcast_jobs.find_one_and_update(
        {"job_id": job_id, "status": "pending_confirmation"},
        {
            "$set": {
                "status": "queued",
                "confirmed_at": _now(),
                "updated_at": _now(),
                "control_chat_id": int(query.message.chat.id) if query.message else None,
                "control_message_id": int(query.message.message_id) if query.message else None,
            }
        },
        return_document=ReturnDocument.AFTER,
    )
    if not updated:
        await query.answer("This broadcast was already handled.", show_alert=True)
        return
    _wakeup.set()
    await query.answer("Broadcast queued.")
    try:
        if query.message:
            await query.message.edit_text(
                "📣 <b>Broadcast queued</b>\n\n"
                f"Job: <code>{job_id}</code>\n"
                "Use <code>/broadcast status</code> to check progress or "
                "<code>/broadcast cancel</code> to request cancellation."
            )
    except Exception:
        log.exception("BROADCAST queue message edit failed job=%s", job_id)


@broadcast_router.my_chat_member()
async def bot_membership_updated(event: ChatMemberUpdated) -> None:
    # ChatRegistryMiddleware records membership state; this handler enables
    # Telegram delivery of my_chat_member updates.
    log.info(
        "CHAT MEMBERSHIP changed chat=%s type=%s status=%s",
        event.chat.id,
        _enum_value(event.chat.type),
        _enum_value(getattr(event.new_chat_member, "status", None)),
    )


def install_broadcast(dispatcher: Dispatcher, root_router: Router) -> None:
    """Attach broadcast commands, chat discovery, and global send-error handling."""
    root_router.include_router(broadcast_router)
    dispatcher.update.outer_middleware(ChatRegistryMiddleware())
    dispatcher.errors.register(_handle_dispatch_error)
