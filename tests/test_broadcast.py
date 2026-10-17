from __future__ import annotations

import unittest

from unified.broadcast import is_broadcast_chat_type, is_send_permission_error


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


if __name__ == "__main__":
    unittest.main()
