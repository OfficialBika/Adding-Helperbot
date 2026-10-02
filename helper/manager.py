from __future__ import annotations

import asyncio
import json
import logging
import re
from pathlib import Path
from dataclasses import dataclass
from typing import Optional

log = logging.getLogger("helper-manager")

STATE_PATH = Path("addhelper_state.json")
DEFAULT_DELAY = 5
MAX_DELAY = 30
CATCH_YOUR_WAIFU_RESPONSE_TIMEOUT = 10
CATCH_YOUR_WAIFU_MAX_MISSES = 20

# Keep the established Adding/Helper source map and command aliases.
SOURCES = {
    "catch": ("@Character_Catcher_Bot", ("/startcatchbot", "/startcatcherbot", "/startcharactercatcher"), ("/resumecatchbot", "/resumecatcherbot", "/resumecharactercatcher")),
    "hallow": ("@Characters_Hallow_bot", ("/starthallowbot", "/starthallow"), ("/resumehallowbot", "/resumehallow")),
    "capture": ("@CaptureCharacterBot", ("/startcapturebot", "/startcapture"), ("/resumecapturebot", "/resumecapture")),
    "seizer": ("@Character_Seizer_Bot", ("/startseizerbot", "/startseizer"), ("/resumeseizerbot", "/resumeseizer")),
    "grab": ("@Grab_Your_Waifu_Bot", ("/startgrabbot", "/startgrabyourwaifu"), ("/resumegrabbot", "/resumegrabyourwaifu")),
    "husbando_grabber": ("@Husbando_Grabber_Bot", ("/starthusbandograbberbot", "/starthusbandograbber"), ("/resumehusbandograbberbot", "/resumehusbandograbber")),
    "takers": ("@Takers_character_bot", ("/starttakersbot", "/starttakers"), ("/resumetakersbot", "/resumetakers")),
    "catch_husbando": ("@Catch_Your_Husbando_Bot", ("/startcatchyourhusbandobot", "/startcatchyourhusbando"), ("/resumecatchyourhusbandobot", "/resumecatchyourhusbando")),
    "smash": ("@Smash_Character_Bot", ("/startsmashbot", "/startsmash"), ("/resumesmashbot", "/resumesmash")),
    "waifux": ("@WaifuxGrabBot", ("/startwaifuxgrabbot", "/startwaifuxgrab", "/startwaifux"), ("/resumewaifuxgrabbot", "/resumewaifuxgrab", "/resumewaifux")),
    "catch_waifu": ("@Catch_Your_Waifu_Bot", ("/startcatchyourwaifubot", "/startcatchyourwaifu"), ("/resumecatchyourwaifubot", "/resumecatchyourwaifu")),
    "waifu_grabber": ("@Waifu_Grabber_Bot", ("/startwaifugrabberbot", "/startwaifugrabber"), ("/resumewaifugrabberbot", "/resumewaifugrabber")),
    "zoro": ("@roronoa_zoro_robot", ("/startzorobot", "/startzoro"), ("/resumezorobot", "/resumezoro")),
    "picker": ("@character_picker_bot", ("/startpickerbot", "/startpicker"), ("/resumepickerbot", "/resumepicker")),
    "senpai": ("@SenpaiCatcherBot", ("/startsenpaibot",), ("/resumesenpaibot",)),
    "bika": ("@BikaCharacterBot", ("/startbika", "/startbikabot"), ("/resumebika", "/resumebikabot")),
    "ziceko": ("@Super_zeko_bot", ("/startzicekobot", "/startziceko"), ("/resumezicekobot", "/resumeziceko")),
    "orin": ("@orinx_catcher_waifu_bot", ("/startorinbot", "/startorin", "/startorinx"), ("/resumeorinbot", "/resumeorin", "/resumeorinx")),
    "dao": ("@ImmortalDonghuaBot", ("/startdaobot", "/startdao", "/startdonghua"), ("/resumedaobot", "/resumedao", "/resumedonghua")),
}

FORWARD_SOURCES = {
    "hallow": "@hallowuploads",
    "capture": "@CaptureDatabase",
    "seizer": "@Seizer_Database",
    "waifux": "@WAIFUXGRAB_DATABASE",
    "senpai": "@fafafawfawfa",
    "catch": "@Character_Catcher_Logs",
    "bika": "-1003923540741",
    "ziceko": "@zicekodata_1",
    "orin": "@timunagalaya",
    "dao": "-1004397263975",
    "picker": "@Picker_database",
    "kairo": "@KairoDatabase",
}

DM_SOURCES = {
    "catch": ("@CharacterCatcherBot", "/check"),
    "grab": ("@GrabGardenBot", "/check"),
    "senpai": ("@SenpaiCatcherBot", "/see"),
    "catch_waifu": ("@Catch_Your_Waifu_Bot", "/w"),
    "hallow": ("@CharacterHallowBot", "/show"),
    "takers": ("@TakersBot", "/detect"),
}

@dataclass
class Runner:
    task: asyncio.Task
    source: str
    mode: str

class HelperManager:
    def __init__(self, runtime):
        self.runtime = runtime
        self.runners: dict[str, Runner] = {}
        self.responses: dict[str, asyncio.Queue] = {}
        self._state = self._load()
        self._bound = False

    def _load(self):
        try:
            return json.loads(STATE_PATH.read_text(encoding="utf-8"))
        except Exception:
            return {}

    def _save(self):
        try:
            payload = json.dumps(self._state, ensure_ascii=False, indent=2)
            # Atomic replace prevents a VPS/PM2 restart from leaving a half-written
            # checkpoint file. This is helper progress only; MongoDB is untouched.
            tmp = STATE_PATH.with_name(f"{STATE_PATH.name}.tmp")
            tmp.write_text(payload, encoding="utf-8")
            tmp.replace(STATE_PATH)
        except Exception:
            log.exception("failed to save helper state")

    def _inline_progress_map(self):
        progress = self._state.get("inline_progress")
        if not isinstance(progress, dict):
            progress = {}
            self._state["inline_progress"] = progress
        return progress

    def _inline_progress(self, key):
        progress = self._inline_progress_map()
        item = progress.get(key)
        if not isinstance(item, dict):
            item = {}
            progress[key] = item
        return item

    @property
    def client(self):
        return self.runtime.client

    def bind(self):
        if self._bound or not self.client:
            return
        self._bound = True
        from pyrogram import filters

        @self.client.on_message(filters.private)
        async def _dm_response(_, message):
            user = getattr(message, "from_user", None)
            username = (getattr(user, "username", "") or "").lower()
            uid = str(getattr(user, "id", "") or "")
            for key, (bot, _) in DM_SOURCES.items():
                if username == bot.lstrip("@").lower() or uid == self._bot_id_for(key):
                    q = self.responses.setdefault(key, asyncio.Queue())
                    await q.put(message)

    def _bot_id_for(self, key):
        return str(self._state.get("dm_bot_ids", {}).get(key, ""))

    def _start_delay(self, text: str) -> int:
        parts = (text or "").strip().split()
        if len(parts) >= 2 and parts[1].isdigit():
            return max(1, min(int(parts[1]), MAX_DELAY))
        return DEFAULT_DELAY

    def _parse(self, text: str):
        """Parse optional delay for start commands and count+delay for resume commands."""
        parts = (text or "").strip().split()
        args = parts[1:]
        numbers = [int(x) for x in args if x.isdigit()]
        if not numbers:
            return None, DEFAULT_DELAY
        if parts[0].lower().split("@", 1)[0].startswith("/resume"):
            count = max(0, numbers[0])
            delay = max(1, min(numbers[1], MAX_DELAY)) if len(numbers) >= 2 else DEFAULT_DELAY
            return count, delay
        delay = max(1, min(numbers[0], MAX_DELAY))
        return None, delay

    def _resume_args(self, text: str):
        count, delay = self._parse(text)
        if count is None:
            raise ValueError("Resume count is required")
        return count, delay

    def _source_for_command(self, cmd: str):
        cmd = cmd.split("@", 1)[0].lower()
        for key, (_, starts, resumes) in SOURCES.items():
            if cmd in starts:
                return key, "start"
            if cmd in resumes:
                return key, "resume"
        return None, None

    async def start_catch_your_waifu(self, start_id: int = 1, delay: int = DEFAULT_DELAY):
        """Sequentially collect Catch_Your_Waifu_Bot /w IDs without inline mode."""
        key = "catch_waifu"
        if key in self.runners and not self.runners[key].task.done():
            raise RuntimeError("catch_waifu is already running")
        start_id = max(1, int(start_id))
        delay = max(1, min(int(delay), MAX_DELAY))
        catch_state = self._state.setdefault("catch_your_waifu_progress", {})
        catch_state.update({
            "source": key,
            "mode": "catch_your_waifu_w",
            "next_id": start_id,
            "pending_id": None,
            "last_success_id": None,
            "consecutive_no_response": 0,
            "delay": delay,
            "response_timeout": CATCH_YOUR_WAIFU_RESPONSE_TIMEOUT,
            "max_no_response": CATCH_YOUR_WAIFU_MAX_MISSES,
            "running": True,
        })
        self._state.update({
            "source": key,
            "mode": "catch_your_waifu_w",
            "next_id": start_id,
            "delay": delay,
            "running": True,
        })
        self._save()
        task = asyncio.create_task(self._catch_your_waifu_worker(start_id, delay))
        self.runners[key] = Runner(task, key, "catch_your_waifu_w")

    async def _catch_your_waifu_worker(self, start_id: int, delay: int):
        key = "catch_waifu"
        bot, command = DM_SOURCES[key]
        catch_state = self._state.setdefault("catch_your_waifu_progress", {})
        current_id = max(1, int(start_id))
        consecutive_no_response = int(catch_state.get("consecutive_no_response", 0) or 0)
        q = self.responses.setdefault(key, asyncio.Queue())
        try:
            while True:
                while not q.empty():
                    try:
                        q.get_nowait()
                    except asyncio.QueueEmpty:
                        break

                catch_state.update({
                    "source": key,
                    "mode": "catch_your_waifu_w",
                    "pending_id": current_id,
                    "next_id": current_id,
                    "delay": delay,
                    "running": True,
                })
                self._save()
                await self.client.send_message(bot, f"{command} {current_id}")
                try:
                    response = await asyncio.wait_for(
                        q.get(), timeout=CATCH_YOUR_WAIFU_RESPONSE_TIMEOUT
                    )
                except asyncio.TimeoutError:
                    consecutive_no_response += 1
                    catch_state.update({
                        "source": key,
                        "mode": "catch_your_waifu_w",
                        "pending_id": None,
                        "last_checked_id": current_id,
                        "next_id": current_id + 1,
                        "consecutive_no_response": consecutive_no_response,
                        "running": True,
                    })
                    self._state.update({
                        "source": key,
                        "mode": "catch_your_waifu_w",
                        "next_id": current_id + 1,
                        "consecutive_no_response": consecutive_no_response,
                        "running": True,
                    })
                    self._save()
                    log.warning(
                        "CatchYourWaifu /w no response id=%s consecutive=%s",
                        current_id,
                        consecutive_no_response,
                    )
                    if consecutive_no_response >= CATCH_YOUR_WAIFU_MAX_MISSES:
                        log.info(
                            "CatchYourWaifu auto-stop after %s consecutive no-response IDs at id=%s",
                            CATCH_YOUR_WAIFU_MAX_MISSES,
                            current_id,
                        )
                        break
                    current_id += 1
                    await asyncio.sleep(delay)
                    continue

                # Any actual bot response resets the no-response streak. Only
                # media-bearing responses are forwarded to Adding because the
                # lookup DB requires media identity; text-only replies are logged
                # and skipped without stopping the sequence.
                consecutive_no_response = 0
                has_media = bool(
                    getattr(response, "photo", None)
                    or getattr(response, "video", None)
                    or getattr(response, "animation", None)
                    or getattr(response, "document", None)
                )
                response_text = "\\n".join(
                    str(v) for v in (
                        getattr(response, "text", None),
                        getattr(response, "caption", None),
                    ) if isinstance(v, str) and v.strip()
                )
                if has_media:
                    await self.client.forward_messages(
                        self.runtime.adding_chat_id,
                        response.chat.id,
                        response.id,
                    )
                    log.info(
                        "CatchYourWaifu forwarded id=%s response=%s text=%r",
                        current_id,
                        response.id,
                        response_text[:180],
                    )
                else:
                    log.info(
                        "CatchYourWaifu response without media id=%s response=%s text=%r",
                        current_id,
                        response.id,
                        response_text[:180],
                    )

                catch_state.update({
                    "source": key,
                    "mode": "catch_your_waifu_w",
                    "pending_id": None,
                    "last_success_id": current_id,
                    "last_checked_id": current_id,
                    "next_id": current_id + 1,
                    "consecutive_no_response": 0,
                    "running": True,
                })
                self._state.update({
                    "source": key,
                    "mode": "catch_your_waifu_w",
                    "next_id": current_id + 1,
                    "consecutive_no_response": 0,
                    "running": True,
                })
                self._save()
                current_id += 1
                await asyncio.sleep(delay)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            self._state["last_error"] = str(exc)
            log.exception("CatchYourWaifu /w helper failed")
        finally:
            catch_state["running"] = False
            catch_state["pending_id"] = None
            self._state["running"] = False
            self._save()
            self.runners.pop(key, None)

    async def start_senpai(self, start_id: int = 1, delay: int = DEFAULT_DELAY):
        """Sequentially collect @SenpaiCatcherBot /see IDs through the helper account."""
        key = "senpai"
        if key in self.runners and not self.runners[key].task.done():
            raise RuntimeError("senpai is already running")
        start_id = max(1, int(start_id))
        delay = max(1, min(int(delay), MAX_DELAY))
        self._state.update({
            "source": key,
            "mode": "senpai_see",
            "next_id": start_id,
            "consecutive_not_found": 0,
            "delay": delay,
            "running": True,
        })
        self._save()
        task = asyncio.create_task(self._senpai_worker(start_id, delay))
        self.runners[key] = Runner(task, key, "senpai_see")

    async def _senpai_worker(self, start_id: int, delay: int):
        key = "senpai"
        bot, _ = DM_SOURCES[key]
        current_id = max(1, int(start_id))
        consecutive_not_found = 0
        q = self.responses.setdefault(key, asyncio.Queue())
        try:
            while True:
                # Never let an old response satisfy a new /see request.
                while not q.empty():
                    try:
                        q.get_nowait()
                    except asyncio.QueueEmpty:
                        break

                await self.client.send_message(bot, f"/see {current_id}")
                try:
                    response = await asyncio.wait_for(q.get(), timeout=45)
                except asyncio.TimeoutError:
                    self._state.update({
                        "source": key,
                        "next_id": current_id,
                        "consecutive_not_found": consecutive_not_found,
                        "last_error": f"timeout waiting for /see {current_id}",
                    })
                    log.warning("Senpai /see timeout id=%s", current_id)
                    break

                response_text = "\n".join(
                    str(v) for v in (
                        getattr(response, "text", None),
                        getattr(response, "caption", None),
                    ) if isinstance(v, str) and v.strip()
                )
                if re.search(r"character\s+with\s+id\s+\d+\s+not\s+found", response_text, re.I):
                    consecutive_not_found += 1
                    self._state.update({
                        "source": key,
                        "mode": "senpai_see",
                        "last_checked_id": current_id,
                        "next_id": current_id + 1,
                        "consecutive_not_found": consecutive_not_found,
                        "running": True,
                    })
                    self._save()
                    log.info("Senpai not found id=%s consecutive=%s", current_id, consecutive_not_found)
                    if consecutive_not_found >= 3:
                        log.info("Senpai auto-stop after 3 consecutive not-found responses at id=%s", current_id)
                        break
                else:
                    consecutive_not_found = 0
                    # Forward the original bot response so Telegram keeps its
                    # media and sender identity. The Adding bot then parses it.
                    await self.client.forward_messages(
                        self.runtime.adding_chat_id,
                        response.chat.id,
                        response.id,
                    )
                    self._state.update({
                        "source": key,
                        "mode": "senpai_see",
                        "last_checked_id": current_id,
                        "next_id": current_id + 1,
                        "consecutive_not_found": 0,
                        "running": True,
                    })
                    self._save()

                current_id += 1
                await asyncio.sleep(delay)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            self._state["last_error"] = str(exc)
            log.exception("Senpai helper failed")
        finally:
            self._state["running"] = False
            self._save()
            self.runners.pop(key, None)

    async def start_inline(
        self,
        key,
        delay=DEFAULT_DELAY,
        resume=False,
        resume_count=None,
        prefer_checkpoint=True,
    ):
        """Run an inline source with per-source, restart-safe pagination checkpoints."""
        if key in self.runners and not self.runners[key].task.done():
            raise RuntimeError(f"{key} is already running")

        bot, _, _ = SOURCES[key]
        delay = max(1, min(int(delay), MAX_DELAY))
        progress = self._inline_progress(key)

        if resume:
            if resume_count is None:
                requested_count = max(0, int(progress.get("completed_count", 0) or 0))
                resume_reason = "saved checkpoint"
            else:
                requested_count = max(0, int(resume_count))
                resume_reason = f"explicit count {requested_count}"
            reset = False
        else:
            requested_count = 0
            resume_reason = "fresh start"
            reset = True

        if reset:
            progress.clear()

        progress.update({
            "source": key,
            "bot": bot,
            "mode": "inline",
            "status": "running",
            "phase": "resolving" if resume else "scanning",
            "resume_reason": resume_reason,
            "requested_count": requested_count,
            "completed_count": requested_count if resume and requested_count else 0,
            "total_items": progress.get("total_items") if resume else None,
            "scanned_count": int(progress.get("scanned_count", 0) or 0) if resume else 0,
            "page_number": int(progress.get("page_number", 1) or 1) if resume else 1,
            "page_offset": str(progress.get("page_offset", "") or "") if resume else "",
            "page_start_count": int(progress.get("page_start_count", 0) or 0) if resume else 0,
            "result_index": int(progress.get("result_index", 0) or 0) if resume else 0,
            "last_result_id": str(progress.get("last_result_id", "") or "") if resume else "",
            "delay": delay,
            "running": True,
            "last_error": "",
        })
        self._state.update({
            "source": key,
            "mode": "inline",
            "current_index": progress["completed_count"],
            "total_items": progress.get("total_items"),
            "delay": delay,
            "running": True,
            "history_scanning": False,
        })
        self._save()

        task = asyncio.create_task(
            self._inline_worker(
                key,
                bot,
                delay,
                resume=resume,
                requested_count=requested_count,
                prefer_checkpoint=prefer_checkpoint,
            )
        )
        self.runners[key] = Runner(task, key, "inline")

    async def _get_inline_page(self, bot, offset=""):
        """Fetch one inline page, waiting through Telegram FloodWaits."""
        from pyrogram.errors import FloodWait

        while True:
            try:
                return await self.client.get_inline_bot_results(
                    bot,
                    "",
                    offset=offset,
                )
            except FloodWait as exc:
                wait_seconds = max(1, int(getattr(exc, "value", 1) or 1))
                log.warning(
                    "inline FloodWait bot=%s offset=%s wait=%ss",
                    bot,
                    offset,
                    wait_seconds,
                )
                await asyncio.sleep(wait_seconds)

    async def _locate_inline_count(self, bot, target):
        """Locate an absolute result position by scanning inline pagination once."""
        offset = ""
        seen = 0
        page_number = 1
        visited_offsets = set()

        while True:
            if offset in visited_offsets:
                raise RuntimeError(
                    f"Inline pagination loop detected for {bot} at offset {offset!r}"
                )
            visited_offsets.add(offset)

            result = await self._get_inline_page(bot, offset)
            results = result.results or []
            n = len(results)

            if n <= 0:
                raise RuntimeError(
                    f"Resume count {target} exceeds available results ({seen})"
                )

            if seen + n > target:
                return offset, target - seen, page_number, seen, seen + n, False

            seen += n
            next_offset = result.next_offset or ""
            if not next_offset:
                if seen == target:
                    return offset, n, page_number, seen - n, seen, True
                raise RuntimeError(
                    f"Resume count {target} exceeds available results ({seen})"
                )

            offset = next_offset
            page_number += 1

    async def _locate_inline_result_id(self, bot, target_id):
        """Find a previously-added result ID and return the position after it."""
        offset = ""
        page_number = 1
        page_start_count = 0
        visited_offsets = set()

        while True:
            if offset in visited_offsets:
                raise RuntimeError(
                    f"Inline pagination loop detected for {bot} at offset {offset!r}"
                )
            visited_offsets.add(offset)

            result = await self._get_inline_page(bot, offset)
            results = result.results or []
            if not results:
                break

            for i, item in enumerate(results):
                if str(getattr(item, "id", "")) == target_id:
                    return (
                        offset,
                        i + 1,
                        page_number,
                        page_start_count,
                        False,
                    )

            page_start_count += len(results)
            next_offset = result.next_offset or ""
            if not next_offset:
                break

            offset = next_offset
            page_number += 1

        return None

    async def _resolve_inline_resume(
        self,
        key,
        bot,
        progress,
        requested_count,
        prefer_checkpoint=True,
    ):
        """Resolve the safest restart point: checkpoint when requested, otherwise count."""
        saved_offset = str(progress.get("page_offset", "") or "")
        saved_index = int(progress.get("result_index", 0) or 0)
        saved_page = int(progress.get("page_number", 1) or 1)
        saved_page_start = int(progress.get("page_start_count", 0) or 0)
        last_result_id = str(progress.get("last_result_id", "") or "")

        # A saved result ID is the strongest checkpoint because inline result
        # pages can move when the source bot changes its database ordering.
        # Explicit /resume <count> always wins over the saved checkpoint.
        if prefer_checkpoint and last_result_id:
            if saved_index > 0:
                result = await self._get_inline_page(bot, saved_offset)
                results = result.results or []
                if (
                    saved_index <= len(results)
                    and str(getattr(results[saved_index - 1], "id", "")) == last_result_id
                ):
                    scanned = max(
                        int(progress.get("scanned_count", 0) or 0),
                        saved_page_start + len(results),
                    )
                    return (
                        saved_offset,
                        saved_index,
                        saved_page,
                        saved_page_start,
                        scanned,
                        False,
                    )

            located = await self._locate_inline_result_id(bot, last_result_id)
            if located:
                offset, index, page, page_start, complete = located
                result = await self._get_inline_page(bot, offset)
                scanned = page_start + len(result.results or [])
                return offset, index, page, page_start, scanned, complete

            log.warning(
                "inline checkpoint result_id=%s no longer exists for %s; "
                "falling back to count=%s",
                last_result_id,
                key,
                requested_count,
            )

        return await self._locate_inline_count(bot, requested_count)

    async def _send_inline_result(self, bot, offset, query_id, result_id):
        """Send one inline result, recovering an expired inline query ID."""
        from pyrogram.errors import FloodWait

        while True:
            try:
                await self.client.send_inline_bot_result(
                    self.runtime.adding_chat_id,
                    query_id,
                    result_id,
                )
                return
            except FloodWait as exc:
                wait_seconds = max(1, int(getattr(exc, "value", 1) or 1))
                log.warning(
                    "inline send FloodWait bot=%s result=%s wait=%ss",
                    bot,
                    result_id,
                    wait_seconds,
                )
                await asyncio.sleep(wait_seconds)
            except Exception as exc:
                error_text = str(exc).upper()
                if "QUERY_ID_INVALID" not in error_text and "QUERY_ID_EXPIRED" not in error_text:
                    raise

                # The query ID can expire while a long page is being drained.
                # Refresh the same page and send the same result ID with the new
                # query ID so the checkpoint can remain exact.
                fresh = await self._get_inline_page(bot, offset)
                fresh_results = fresh.results or []
                if not any(str(getattr(item, "id", "")) == str(result_id) for item in fresh_results):
                    raise RuntimeError(
                        f"Inline result {result_id} disappeared from {bot} "
                        f"while refreshing an expired query ID"
                    ) from exc
                query_id = fresh.query_id

    async def _inline_worker(
        self,
        key,
        bot,
        delay,
        resume=False,
        requested_count=0,
        prefer_checkpoint=True,
    ):
        progress = self._inline_progress(key)
        try:
            if resume:
                (
                    offset,
                    index,
                    page_number,
                    page_start_count,
                    discovered,
                    complete,
                ) = await self._resolve_inline_resume(
                    key,
                    bot,
                    progress,
                    requested_count,
                    prefer_checkpoint=prefer_checkpoint,
                )
            else:
                offset = ""
                index = 0
                page_number = 1
                page_start_count = 0
                discovered = 0
                complete = False

            if complete:
                progress.update({
                    "status": "complete",
                    "phase": "complete",
                    "running": False,
                    "completed_count": requested_count,
                    "total_items": discovered,
                    "scanned_count": discovered,
                    "page_number": page_number,
                    "page_offset": offset,
                    "page_start_count": page_start_count,
                    "result_index": index,
                    "last_error": "",
                })
                self._state.update({
                    "source": key,
                    "mode": "inline",
                    "current_index": progress["completed_count"],
                    "total_items": progress["total_items"],
                    "running": False,
                    "history_scanning": False,
                })
                self._save()
                return

            progress.update({
                "status": "running",
                "phase": "scanning",
                "page_number": page_number,
                "page_offset": offset,
                "page_start_count": page_start_count,
                "result_index": index,
                "scanned_count": max(int(progress.get("scanned_count", 0) or 0), discovered),
                "last_error": "",
                "running": True,
            })
            self._state.update({
                "current_index": progress.get("completed_count", 0),
                "total_items": progress.get("total_items"),
                "running": True,
            })
            self._save()

            visited_offsets = set()
            while True:
                if offset in visited_offsets:
                    raise RuntimeError(
                        f"Inline pagination loop detected for {bot} at offset {offset!r}"
                    )
                visited_offsets.add(offset)

                result = await self._get_inline_page(bot, offset)
                results = result.results or []
                if not results:
                    total = max(
                        int(progress.get("scanned_count", 0) or 0),
                        page_start_count,
                    )
                    progress.update({
                        "status": "complete",
                        "phase": "complete",
                        "running": False,
                        "completed_count": min(
                            int(progress.get("completed_count", 0) or 0),
                            total,
                        ),
                        "total_items": total,
                        "scanned_count": total,
                        "result_index": 0,
                        "last_error": "",
                    })
                    self._state.update({
                        "source": key,
                        "mode": "inline",
                        "current_index": progress["completed_count"],
                        "total_items": total,
                        "running": False,
                    })
                    self._save()
                    return

                discovered = max(discovered, page_start_count + len(results))
                progress.update({
                    "page_number": page_number,
                    "page_offset": offset,
                    "page_start_count": page_start_count,
                    "result_index": index,
                    "scanned_count": discovered,
                    "total_items": None,
                    "phase": "scanning",
                    "running": True,
                })
                self._state.update({
                    "source": key,
                    "mode": "inline",
                    "current_index": progress.get("completed_count", 0),
                    "total_items": None,
                    "running": True,
                })
                self._save()

                for i in range(max(0, index), len(results)):
                    item = results[i]
                    result_id = str(getattr(item, "id", "") or "")
                    if not result_id:
                        raise RuntimeError(
                            f"Inline result at page {page_number}, index {i} "
                            f"has no result ID"
                        )

                    await self._send_inline_result(
                        bot,
                        offset,
                        result.query_id,
                        result_id,
                    )

                    completed_count = page_start_count + i + 1
                    progress.update({
                        "page_number": page_number,
                        "page_offset": offset,
                        "page_start_count": page_start_count,
                        "result_index": i + 1,
                        "completed_count": completed_count,
                        "scanned_count": discovered,
                        "total_items": None,
                        "last_result_id": result_id,
                        "phase": "scanning",
                        "status": "running",
                        "running": True,
                        "last_error": "",
                    })
                    self._state.update({
                        "source": key,
                        "mode": "inline",
                        "current_index": completed_count,
                        "total_items": None,
                        "running": True,
                    })
                    self._save()
                    await asyncio.sleep(delay)

                next_offset = result.next_offset or ""
                if not next_offset:
                    total = page_start_count + len(results)
                    progress.update({
                        "source": key,
                        "status": "complete",
                        "phase": "complete",
                        "running": False,
                        "completed_count": total,
                        "total_items": total,
                        "scanned_count": total,
                        "page_number": page_number,
                        "page_offset": offset,
                        "page_start_count": page_start_count,
                        "result_index": len(results),
                        "last_error": "",
                    })
                    self._state.update({
                        "source": key,
                        "mode": "inline",
                        "current_index": total,
                        "total_items": total,
                        "running": False,
                        "history_scanning": False,
                    })
                    self._save()
                    return

                page_start_count += len(results)
                page_number += 1
                offset = next_offset
                index = 0

                # Persist the next page before fetching it. A restart between
                # pages therefore resumes exactly at the first result of the
                # next page instead of replaying the previous page.
                progress.update({
                    "page_number": page_number,
                    "page_offset": offset,
                    "page_start_count": page_start_count,
                    "result_index": 0,
                    "completed_count": page_start_count,
                    "scanned_count": discovered,
                    "total_items": None,
                    "phase": "scanning",
                    "running": True,
                })
                self._state.update({
                    "source": key,
                    "mode": "inline",
                    "current_index": page_start_count,
                    "total_items": None,
                    "running": True,
                })
                self._save()
        except asyncio.CancelledError:
            progress["status"] = "stopped"
            progress["phase"] = "paused"
            progress["running"] = False
            progress["last_error"] = ""
            self._save()
            raise
        except Exception as exc:
            progress["status"] = "error"
            progress["phase"] = "paused"
            progress["running"] = False
            progress["last_error"] = str(exc)
            self._state.update({
                "source": key,
                "mode": "inline",
                "current_index": progress.get("completed_count", 0),
                "total_items": progress.get("total_items"),
                "running": False,
                "history_scanning": False,
            })
            self._save()
            log.exception("inline helper failed: %s", key)
        finally:
            if not asyncio.current_task().cancelled():
                progress["running"] = False
                self._save()
            self.runners.pop(key, None)
    async def start_forward(
        self,
        key,
        delay=DEFAULT_DELAY,
        resume_count=None,
        media_filter=None,
    ):
        source = FORWARD_SOURCES.get(key)
        if not source:
            raise RuntimeError(f"No forward source configured for {key}")
        if key in self.runners and not self.runners[key].task.done():
            raise RuntimeError(f"{key} is already running")

        start = max(0, int(resume_count or 0))
        delay = max(1, min(int(delay), MAX_DELAY))
        media_filter = str(media_filter or "").strip().lower() or None

        if media_filter not in {None, "video"}:
            raise ValueError(f"Unsupported media filter: {media_filter}")

        state_mode = "forward_video" if media_filter == "video" else "forward"

        # IMPORTANT: never scan Telegram history inside the command handler.
        # GetHistory is rate-limited and can take many seconds; doing it here
        # makes /startfw... appear to hang and prevents the bot from replying.
        forward_progress = self._state.setdefault("forward_progress", {})
        forward_progress[key] = {
            "source": key,
            "mode": state_mode,
            "media_filter": media_filter,
            "current_index": start,
            "total_items": None,
            "delay": delay,
            "running": True,
            "history_scanning": True,
        }
        self._state.update({
            "source": key,
            "mode": state_mode,
            "media_filter": media_filter,
            "current_index": start,
            "delay": delay,
            "running": True,
            "last_error": "",
            "history_scanning": True,
        })
        self._save()

        task = asyncio.create_task(
            self._forward_worker(
                key,
                source,
                start,
                delay,
                media_filter=media_filter,
            )
        )
        self.runners[key] = Runner(task, key, state_mode)

    async def _forward_worker(
        self,
        key,
        source,
        start,
        delay,
        media_filter=None,
    ):
        media = []
        forward_progress = self._state.setdefault("forward_progress", {}).setdefault(key, {})
        try:
            # Telegram returns chat history newest -> oldest. Build the media
            # message-ID list in the background, then reverse it so forwarding
            # remains chronological exactly like the previous implementation.
            async for msg in self.client.get_chat_history(source):
                if media_filter == "video":
                    if getattr(msg, "video", None):
                        media.append(int(msg.id))
                elif msg.media:
                    media.append(int(msg.id))

            media.reverse()
            total = len(media)

            if start >= total:
                raise RuntimeError(
                    f"Resume index {start} is at/after the end ({total})"
                )

            state_mode = "forward_video" if media_filter == "video" else "forward"
            forward_progress.update({
                "source": key,
                "mode": state_mode,
                "media_filter": media_filter,
                "current_index": start,
                "total_items": total,
                "delay": delay,
                "running": True,
                "history_scanning": False,
            })
            self._state.update({
                "source": key,
                "mode": state_mode,
                "media_filter": media_filter,
                "current_index": start,
                "total_items": total,
                "delay": delay,
                "running": True,
                "history_scanning": False,
                "last_error": "",
            })
            self._save()

            for i in range(start, total):
                await self.client.forward_messages(
                    self.runtime.adding_chat_id,
                    source,
                    media[i],
                )
                forward_progress.update({
                    "source": key,
                    "mode": state_mode,
                    "media_filter": media_filter,
                    "current_index": i + 1,
                    "total_items": total,
                    "delay": delay,
                    "running": True,
                    "history_scanning": False,
                })
                self._state.update({
                    "source": key,
                    "mode": state_mode,
                    "media_filter": media_filter,
                    "current_index": i + 1,
                    "total_items": total,
                    "running": True,
                    "history_scanning": False,
                })
                self._save()
                await asyncio.sleep(delay)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            self._state["last_error"] = str(exc)
            self._state["history_scanning"] = False
            log.exception("forward helper failed: %s", key)
        finally:
            forward_progress["running"] = False
            forward_progress["history_scanning"] = False
            self._state["running"] = False
            self._state["history_scanning"] = False
            self._save()
            self.runners.pop(key, None)

    async def stop_all(self):
        for r in list(self.runners.values()):
            r.task.cancel()
        if self.runners:
            await asyncio.gather(*(r.task for r in list(self.runners.values())), return_exceptions=True)
        self.runners.clear()
        self._state["running"] = False
        self._save()

    async def status_text(self):
        running = [r.source for r in self.runners.values() if not r.task.done()]
        lines = [
            "🛠 <b>HELPER STATUS</b>",
            f"Running: <code>{'YES' if running else 'NO'}</code>",
            f"Jobs: <code>{', '.join(running) or '-'}</code>",
            "",
            "<b>INLINE CHECKPOINTS</b>",
        ]

        inline = self._state.get("inline_progress") or {}
        if isinstance(inline, dict) and inline:
            for key in SOURCES:
                progress = inline.get(key)
                if not isinstance(progress, dict):
                    continue
                status = str(progress.get("status") or "idle")
                completed = int(progress.get("completed_count", 0) or 0)
                total = progress.get("total_items")
                scanned = int(progress.get("scanned_count", 0) or 0)
                if total is not None:
                    total = int(total or 0)
                    percent = (completed / total * 100.0) if total else 100.0
                    progress_text = f"{completed:,}/{total:,} ({percent:.1f}%)"
                elif scanned:
                    progress_text = f"{completed:,}/{scanned:,}+"
                else:
                    progress_text = f"{completed:,}/-"

                next_number = completed + 1
                page = int(progress.get("page_number", 1) or 1)
                result_index = int(progress.get("result_index", 0) or 0)
                last_id = str(progress.get("last_result_id", "") or "—")
                if len(last_id) > 24:
                    last_id = last_id[:21] + "..."

                lines.extend([
                    f"• <b>{key}</b> — <code>{status}</code>",
                    f"  Progress: <code>{progress_text}</code>",
                    f"  Page/Index: <code>{page}/{result_index}</code>",
                    f"  Resume from: <code>#{next_number:,}</code>",
                    f"  Last result: <code>{last_id}</code>",
                ])
        else:
            lines.append("• <code>No inline checkpoint yet.</code>")

        lines.extend([
            "",
            "<b>ACTIVE/LEGACY HELPER</b>",
            f"Mode: <code>{self._state.get('mode', '-')}</code>",
            f"Source: <code>{self._state.get('source', '-')}</code>",
            f"Index: <code>{self._state.get('current_index', 0)}</code>",
            f"Total: <code>{self._state.get('total_items', '-')}</code>",
            f"History scan: <code>{'YES' if self._state.get('history_scanning') else 'NO'}</code>",
            f"Media filter: <code>{self._state.get('media_filter') or 'all'}</code>",
            f"Next ID: <code>{self._state.get('next_id', '-')}</code>",
            f"Not Found Streak: <code>{self._state.get('consecutive_not_found', 0)}</code>",
            f"Delay: <code>{self._state.get('delay', DEFAULT_DELAY)}s</code>",
            f"Last error: <code>{str(self._state.get('last_error', '-') or '-')}</code>",
        ])
        return "\n".join(lines)

    async def handle_command(self, message):
        text = (message.text or "").strip()
        cmd = text.split()[0].split("@", 1)[0].lower() if text else ""
        if cmd in {"/helperstatus", "/addhelperstatus"}:
            await message.reply(await self.status_text())
            return True
        if cmd in {"/addhelper", "/helper", "/starthelper"}:
            await message.reply(self.help_text())
            return True
        if cmd in {"/stophelper", "/stopinlinebot"}:
            await self.stop_all()
            await message.reply("AddHelper stopped.")
            return True
        if cmd in {"/resethelperprogress", "/resetinlineprogress"}:
            self._state.clear()
            self._save()
            await message.reply("AddHelper progress cleared.")
            return True
        # Catch_Your_Waifu_Bot is deliberately DM-sequential, not inline.
        if cmd in {"/startcatchyourwaifubot", "/startcatchyourwaifu"}:
            try:
                delay = self._start_delay(text)
                await self.start_catch_your_waifu(1, delay)
                await message.reply(
                    "✅ Started Catch Your Waifu /w from <code>1</code>.\\n"
                    f"Source: {DM_SOURCES['catch_waifu'][0]}\\n"
                    f"Command: <code>{DM_SOURCES['catch_waifu'][1]} N</code>\\n"
                    f"Delay: {delay}s\\n"
                    f"Response timeout: {CATCH_YOUR_WAIFU_RESPONSE_TIMEOUT}s\\n"
                    f"Auto-stop: {CATCH_YOUR_WAIFU_MAX_MISSES} consecutive no-response IDs."
                )
            except Exception as exc:
                await message.reply(f"Catch Your Waifu helper error: {exc}")
            return True

        if cmd in {"/resumecatchyourwaifubot", "/resumecatchyourwaifu"}:
            try:
                catch_state = self._state.get("catch_your_waifu_progress") or {}
                # If the process stopped while waiting for a response, retry the
                # exact pending ID instead of skipping it.
                start_id = max(1, int(catch_state.get("pending_id") or catch_state.get("next_id") or 1))
                delay = max(1, min(int(catch_state.get("delay", DEFAULT_DELAY) or DEFAULT_DELAY), MAX_DELAY))
                await self.start_catch_your_waifu(start_id, delay)
                await message.reply(
                    f"✅ Resumed Catch Your Waifu /w from <code>{start_id}</code>.\\n"
                    f"Delay: {delay}s\\n"
                    f"Auto-stop: {CATCH_YOUR_WAIFU_MAX_MISSES} consecutive no-response IDs."
                )
            except Exception as exc:
                await message.reply(f"Catch Your Waifu helper error: {exc}")
            return True

        key, kind = self._source_for_command(cmd)
        if kind:
            count, delay = self._parse(text)
            try:
                if key == "senpai":
                    if kind == "resume":
                        start_id = max(1, int(count or 1))
                        await self.start_senpai(start_id, delay)
                        await message.reply(
                            f"Resumed senpai /see from ID {start_id}.\\n"
                            f"Delay: {delay}s\\n"
                            "Auto-stop: 3 consecutive not-found responses."
                        )
                    else:
                        await self.start_senpai(1, delay)
                        await message.reply(
                            "Started Senpai /see from ID 1.\\n"
                            f"Delay: {delay}s\\n"
                            "Auto-stop: 3 consecutive not-found responses."
                        )
                elif kind == "resume":
                    await self.start_inline(
                        key,
                        delay,
                        resume=True,
                        resume_count=count,
                        prefer_checkpoint=count is None,
                    )
                    checkpoint = self._inline_progress(key)
                    start_from = int(checkpoint.get("completed_count", 0) or 0)
                    mode_text = "saved checkpoint" if count is None else f"explicit count {count}"
                    await message.reply(
                        f"✅ Resumed {key} from <code>#{start_from:,}</code>.\n"
                        f"Mode: {mode_text}\n"
                        f"Source: {SOURCES[key][0]}\n"
                        f"Delay: {delay}s\n"
                        "Checkpoint will update after every result."
                    )
                else:
                    await self.start_inline(key, delay, resume=False)
                    await message.reply(
                        f"✅ Started {key} from <code>#0</code>.\n"
                        f"Source: {SOURCES[key][0]}\n"
                        f"Delay: {delay}s\n"
                        "Existing progress for this source was reset; other sources are untouched."
                    )
            except Exception as exc:
                await message.reply(f"Helper error: {exc}")
            return True
        # Catch FW video-only backfill. This is deliberately separate from
        # the normal Catch FW command so /startfwcatchbot keeps its exact behavior.
        if cmd == "/startfwcatchbotvd":
            try:
                delay = self._start_delay(text)
                await self.start_forward(
                    "catch",
                    delay=delay,
                    media_filter="video",
                )
                await message.reply(
                    "✅ Started forward catch (VIDEO ONLY).\n"
                    f"Source: {FORWARD_SOURCES['catch']}\n"
                    f"Delay: {delay}s\n"
                    "Photo/Animation/Document posts are skipped.\n"
                    "History scan is running in background."
                )
            except Exception as exc:
                await message.reply(f"Forward helper error: {exc}")
            return True

        for key, source in FORWARD_SOURCES.items():
            starts = (f"/startfw{key}bot", f"/startfw{key}")
            resumes = (f"/resumefw{key}bot", f"/resumefw{key}")
            if cmd in starts or cmd in resumes:
                try:
                    if cmd in resumes:
                        # Catch FW can resume from its persisted helper index
                        # when no count is supplied; an explicit count still wins.
                        if (
                            key == "catch"
                            and len((text or "").split()) == 1
                            and self._state.get("source") == key
                            and self._state.get("mode") == "forward"
                        ):
                            count = max(0, int(self._state.get("current_index", 0) or 0))
                            delay = max(1, min(int(self._state.get("delay", DEFAULT_DELAY) or DEFAULT_DELAY), MAX_DELAY))
                        else:
                            count, delay = self._resume_args(text)
                    else:
                        count, delay = None, self._start_delay(text)
                    await self.start_forward(key, delay, count if cmd in resumes else None)
                    action = "Resumed" if cmd in resumes else "Started"
                    if cmd in resumes and count is not None:
                        detail = f" from index {count}"
                    else:
                        detail = ""
                    await message.reply(
                        f"✅ {action} forward {key}{detail}.\n"
                        f"Source: {source}\n"
                        f"Delay: {delay}s\n"
                        "History scan is running in background."
                    )
                except Exception as exc:
                    await message.reply(f"Forward helper error: {exc}")
                return True
        return False

    def help_text(self):
        return (
            "AddHelper ready ✅\n\n"
            "/startcatchbot [delay]\n"
            "/resumecatchbot [count] [delay]\n"
            "/starthallowbot [delay]\n"
            "/resumehallowbot [count] [delay]\n"
            "/startcapturebot [delay]\n"
            "/resumecapturebot [count] [delay]\n"
            "/startseizerbot [delay]\n"
            "/resumeseizerbot [count] [delay]\n"
            "/startgrabbot [delay]\n"
            "/resumegrabbot [count] [delay]\n"
            "/starttakersbot [delay]\n"
            "/resumetakersbot [count] [delay]\n"
            "/startpickerbot [delay]\n"
            "/resumepickerbot [count] [delay]\n"
            "/startzicekobot [delay]\n"
            "/resumezicekobot [count] [delay]\n"
            "/startorinbot [delay]\n"
            "/resumeorinbot [count] [delay]\n"
            "/startdaobot [delay]\n"
            "/resumedaobot [count] [delay]\n"
            "/startsenpaibot [delay]\n"
            "/startcatchyourwaifubot [delay]  (DM /w 1, /w 2, ...; no inline)\n"
            "/resumecatchyourwaifubot [delay]  (saved next ID)\n"
            "/resumesenpaibot &lt;next_id&gt; [delay]\n"
            "/startfwpickerbot [delay]\n"
            "/resumefwpickerbot <count> [delay]\n"
            "/startfwkairobot [delay]\n"
            "/resumefwkairobot <count> [delay]\n"
            "/startfwcatchbot [delay]\n"
            "/startfwcatchbotvd [delay]  (video only)\n"
            "/resumefwcatchbot &lt;count&gt; [delay]\n\n"
            "Controls: /helperstatus /stophelper /resethelperprogress"
        )
