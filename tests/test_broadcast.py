from __future__ import annotations

import unittest
from types import SimpleNamespace
from unittest.mock import AsyncMock, patch

from unified.broadcast import (
    auto_leave_restricted_group,
    is_broadcast_chat_type,
    is_send_permission_error,
)


class BroadcastSafetyTests(unittest.TestCase):
    def test_restricted_text_send_is_detected(self):
        self.assertTrue(
            is_send_permission_error(
                "Telegram server says - Bad Request: not enough rights to send text messages to the chat"
            )
        )

    def test_known_write_forbidden_variants_are_detected(self):
        self.assertTrue(is_send_permission_error("Forbidden: chat_write_forbidden"))
        self.assertTrue(is_send_permission_error("not enough rights to send messages"))

    def test_unrelated_telegram_errors_are_not_treated_as_permission_errors(self):
        self.assertFalse(is_send_permission_error("Bad Request: message is not modified"))
        self.assertFalse(is_send_permission_error("Bad Request: chat not found"))
        self.assertFalse(is_send_permission_error("Bad Request: can't parse entities"))

    def test_supported_broadcast_destinations(self):
        for chat_type in ("private", "group", "supergroup"):
            with self.subTest(chat_type=chat_type):
                self.assertTrue(is_broadcast_chat_type(chat_type))

    def test_channels_and_invalid_types_are_not_broadcast_destinations(self):
        for chat_type in ("channel", "unknown", None):
            with self.subTest(chat_type=chat_type):
                self.assertFalse(is_broadcast_chat_type(chat_type))


class AutoLeaveTests(unittest.IsolatedAsyncioTestCase):
    async def test_send_permission_error_makes_bot_leave_a_group(self):
        bot = SimpleNamespace(leave_chat=AsyncMock(return_value=True))
        chat = SimpleNamespace(id=-100123, type="supergroup", title="Test group", username=None)
        with patch("unified.broadcast.bot_chats.update_one", new=AsyncMock()) as update_one:
            result = await auto_leave_restricted_group(
                bot,
                chat,
                "Bad Request: not enough rights to send text messages to the chat",
            )
        self.assertTrue(result)
        bot.leave_chat.assert_awaited_once_with(chat_id=-100123)
        update_one.assert_awaited_once()

    async def test_private_chat_is_never_left(self):
        bot = SimpleNamespace(leave_chat=AsyncMock(return_value=True))
        chat = SimpleNamespace(id=123, type="private", title=None, username=None)
        result = await auto_leave_restricted_group(
            bot,
            chat,
            "Bad Request: not enough rights to send text messages to the chat",
        )
        self.assertFalse(result)
        bot.leave_chat.assert_not_awaited()

    async def test_unrelated_group_error_does_not_trigger_leave(self):
        bot = SimpleNamespace(leave_chat=AsyncMock(return_value=True))
        chat = SimpleNamespace(id=-100123, type="supergroup", title="Test group", username=None)
        result = await auto_leave_restricted_group(
            bot,
            chat,
            "Bad Request: can't parse entities",
        )
        self.assertFalse(result)
        bot.leave_chat.assert_not_awaited()


class _AsyncCursor:
    def __init__(self, rows):
        self.rows = rows

    def sort(self, *args, **kwargs):
        return self

    def batch_size(self, *args, **kwargs):
        return self

    def __aiter__(self):
        self._iterator = iter(self.rows)
        return self

    async def __anext__(self):
        try:
            return next(self._iterator)
        except StopIteration:
            raise StopAsyncIteration


class BroadcastRetentionTests(unittest.IsolatedAsyncioTestCase):
    async def test_cleanup_schedules_only_terminal_jobs_and_their_deliveries(self):
        from datetime import datetime, timedelta, timezone
        from unified.broadcast import cleanup_broadcast_data_once

        now = datetime.now(timezone.utc)
        cursor = _AsyncCursor([
            {"job_id": "finished", "completed_at": now - timedelta(days=40)},
        ])
        jobs = SimpleNamespace(
            find=unittest.mock.Mock(return_value=cursor),
            update_one=AsyncMock(return_value=SimpleNamespace(modified_count=1)),
        )
        deliveries = SimpleNamespace(update_many=AsyncMock())
        with patch("unified.broadcast.broadcast_jobs", jobs), patch(
            "unified.broadcast.broadcast_deliveries", deliveries
        ), patch("unified.broadcast.settings", SimpleNamespace(broadcast_data_retention_days=30)):
            scheduled = await cleanup_broadcast_data_once()

        self.assertNotIn("running", jobs.find.call_args.args[0]["status"]["$in"])
        self.assertEqual(scheduled, 1)
        jobs.update_one.assert_awaited_once()
        deliveries.update_many.assert_awaited_once()
        self.assertEqual(jobs.update_one.await_args.args[0]["job_id"], "finished")
        self.assertEqual(deliveries.update_many.await_args.args[0]["job_id"], "finished")

    async def test_cleanup_does_not_schedule_delivery_if_job_was_not_claimed(self):
        from datetime import datetime, timezone
        from unified.broadcast import cleanup_broadcast_data_once

        cursor = _AsyncCursor([{"job_id": "already-updated", "updated_at": datetime.now(timezone.utc)}])
        jobs = SimpleNamespace(
            find=unittest.mock.Mock(return_value=cursor),
            update_one=AsyncMock(return_value=SimpleNamespace(modified_count=0)),
        )
        deliveries = SimpleNamespace(update_many=AsyncMock())
        with patch("unified.broadcast.broadcast_jobs", jobs), patch(
            "unified.broadcast.broadcast_deliveries", deliveries
        ):
            scheduled = await cleanup_broadcast_data_once()

        self.assertEqual(scheduled, 0)
        deliveries.update_many.assert_not_awaited()


if __name__ == "__main__":
    unittest.main()
