from __future__ import annotations

import asyncio
import os
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, patch

os.environ.setdefault("MONGO_URI", "mongodb://127.0.0.1:27017")
os.environ.setdefault("DB_NAME", "ci_test")

from unified.local_file_cache import LocalFilePathCache
import unified.lookup as lookup


class LocalFilePathCacheTests(unittest.TestCase):
    def test_unique_id_mapping_bypasses_get_file_for_a_different_file_id(self):
        async def run():
            with tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp)
                root = base / "bot-api-data"
                image = root / "bot" / "photos" / "file_123.jpg"
                image.parent.mkdir(parents=True)
                image.write_bytes(b"known-local-image")
                db_path = base / "path-cache.sqlite3"

                writer = LocalFilePathCache(db_path)
                record = writer.remember(root, "OLD-FILE-ID", "STABLE-UNIQUE-ID", image)
                self.assertIsNotNone(record)
                await writer.persist(record)

                # A new cache instance proves the path mapping survives restarts.
                reader = LocalFilePathCache(db_path)
                bot = SimpleNamespace(
                    get_file=AsyncMock(
                        side_effect=AssertionError("getFile must be bypassed on a cache hit")
                    ),
                    download=AsyncMock(
                        side_effect=AssertionError("HTTP download must not run on a cache hit")
                    ),
                )
                fake_settings = SimpleNamespace(
                    bot_api_is_local=True,
                    bot_api_local_files_root=str(root),
                    download_timeout_seconds=20,
                )
                with (
                    patch.object(lookup, "_LOCAL_FILE_PATH_CACHE", reader),
                    patch.object(lookup, "settings", fake_settings),
                ):
                    result = await lookup._download(
                        bot,
                        "DIFFERENT-FILE-ID",
                        file_unique_id="STABLE-UNIQUE-ID",
                    )

                self.assertEqual(result, b"known-local-image")
                bot.get_file.assert_not_awaited()
                bot.download.assert_not_awaited()

        asyncio.run(run())

    def test_get_file_miss_learns_mapping_for_future_id_and_unique_id_hits(self):
        async def run():
            with tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp)
                root = base / "bot-api-data"
                image = root / "bot" / "photos" / "file_456.jpg"
                image.parent.mkdir(parents=True)
                image.write_bytes(b"first-file-bytes")
                cache = LocalFilePathCache(base / "path-cache.sqlite3")
                bot = SimpleNamespace(
                    get_file=AsyncMock(
                        return_value=SimpleNamespace(file_path=str(image))
                    ),
                    download=AsyncMock(),
                )
                fake_settings = SimpleNamespace(
                    bot_api_is_local=True,
                    bot_api_local_files_root=str(root),
                    download_timeout_seconds=20,
                )
                with (
                    patch.object(lookup, "_LOCAL_FILE_PATH_CACHE", cache),
                    patch.object(lookup, "settings", fake_settings),
                ):
                    first = await lookup._download(
                        bot, "FIRST-ID", file_unique_id="PHOTO-UID"
                    )
                    self.assertEqual(first, b"first-file-bytes")
                    bot.get_file.assert_awaited_once_with("FIRST-ID")

                    second = await lookup._download(
                        bot, "SECOND-ID", file_unique_id="PHOTO-UID"
                    )

                self.assertEqual(second, b"first-file-bytes")
                bot.get_file.assert_awaited_once_with("FIRST-ID")
                bot.download.assert_not_awaited()

        asyncio.run(run())

    def test_stale_mapping_is_rejected_and_get_file_fallback_is_kept(self):
        async def run():
            with tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp)
                root = base / "bot-api-data"
                old_image = root / "bot" / "photos" / "old.jpg"
                new_image = root / "bot" / "photos" / "new.jpg"
                old_image.parent.mkdir(parents=True)
                old_image.write_bytes(b"old")
                new_image.write_bytes(b"new-file-bytes")
                cache = LocalFilePathCache(base / "path-cache.sqlite3")
                record = cache.remember(root, "SAME-ID", "SAME-UID", old_image)
                self.assertIsNotNone(record)
                await cache.persist(record)
                old_image.unlink()

                bot = SimpleNamespace(
                    get_file=AsyncMock(
                        return_value=SimpleNamespace(file_path=str(new_image))
                    ),
                    download=AsyncMock(),
                )
                fake_settings = SimpleNamespace(
                    bot_api_is_local=True,
                    bot_api_local_files_root=str(root),
                    download_timeout_seconds=20,
                )
                with (
                    patch.object(lookup, "_LOCAL_FILE_PATH_CACHE", cache),
                    patch.object(lookup, "settings", fake_settings),
                ):
                    result = await lookup._download(
                        bot, "SAME-ID", file_unique_id="SAME-UID"
                    )

                self.assertEqual(result, b"new-file-bytes")
                bot.get_file.assert_awaited_once_with("SAME-ID")
                bot.download.assert_not_awaited()

        asyncio.run(run())

    def test_exact_uid_cache_hit_never_enters_hash_or_file_download(self):
        async def run():
            message = SimpleNamespace(message_id=101)
            media = SimpleNamespace(
                source_message=message,
                media_type="photo",
                obj=SimpleNamespace(file_id="FILE-ID", file_unique_id="UID-101"),
            )
            bot = SimpleNamespace(
                get_file=AsyncMock(),
                download=AsyncMock(),
            )
            expected = {
                "name": "Cached character",
                "command": "/name",
                "source_key": "items_character_catcher",
                "media_type": "photo",
            }
            with (
                patch("unified.lookup.extract_media", return_value=media),
                patch("unified.lookup._scope", return_value=["items_character_catcher"]),
                patch("unified.lookup._telegram_uids", return_value=["UID-101"]),
                patch("unified.lookup._cache_lookup", return_value=expected),
                patch("unified.lookup._hash_fallback", new=AsyncMock()) as hash_fallback,
            ):
                doc, reason = await lookup.lookup_message(bot, message)

            self.assertEqual(doc["name"], "Cached character")
            self.assertEqual(reason, "uid_cache")
            hash_fallback.assert_not_awaited()
            bot.get_file.assert_not_awaited()
            bot.download.assert_not_awaited()

        asyncio.run(run())


if __name__ == "__main__":
    unittest.main()
