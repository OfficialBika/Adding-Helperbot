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
    "bika": "-1003923540741",
    "ziceko": "@zicekodata_1",
    "orin": "@timunagalaya",
    "dao": "-1004397263975",
}

DM_SOURCES = {
    "catch": ("@CharacterCatcherBot", "/check"),
    "grab": ("@GrabGardenBot", "/check"),
    "senpai": ("@SenpaiCatcherBot", "/see"),
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
            STATE_PATH.write_text(json.dumps(self._state, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception:
            log.exception("failed to save helper state")

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

    async def start_inline(self, key, delay=DEFAULT_DELAY, resume_count=None):
        if key in self.runners and not self.runners[key].task.done():
            raise RuntimeError(f"{key} is already running")
        bot, _, _ = SOURCES[key]
        delay = max(1, min(int(delay), MAX_DELAY))
        offset = ""
        index = 0
        sent = int(resume_count or 0)
        if resume_count:
            offset, index = await self._locate(bot, int(resume_count))
        self._state.update({"source": key, "mode": "inline", "current_index": sent, "delay": delay, "running": True})
        self._save()
        task = asyncio.create_task(self._inline_worker(key, bot, delay, offset, index, sent))
        self.runners[key] = Runner(task, key, "inline")

    async def _locate(self, bot, target):
        offset = ""
        seen = 0
        while True:
            result = await self.client.get_inline_bot_results(bot, "", offset=offset)
            n = len(result.results or [])
            if n <= 0:
                raise RuntimeError(f"Resume count {target} exceeds available results ({seen})")
            if seen + n > target:
                return offset, target - seen
            seen += n
            offset = result.next_offset or ""
            if not offset:
                raise RuntimeError(f"Resume count {target} exceeds available results ({seen})")

    async def _inline_worker(self, key, bot, delay, offset, index, sent):
        try:
            while True:
                result = await self.client.get_inline_bot_results(bot, "", offset=offset)
                results = result.results or []
                if not results:
                    break
                for i in range(max(0, index), len(results)):
                    if asyncio.current_task().cancelled():
                        return
                    await self.client.send_inline_bot_result(
                        self.runtime.adding_chat_id,
                        result.query_id,
                        results[i].id,
                    )
                    sent += 1
                    self._state.update({"source": key, "current_index": sent, "running": True})
                    self._save()
                    await asyncio.sleep(delay)
                offset = result.next_offset or ""
                index = 0
                if not offset:
                    break
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            self._state["last_error"] = str(exc)
            log.exception("inline helper failed: %s", key)
        finally:
            self._state["running"] = False
            self._save()
            self.runners.pop(key, None)

    async def start_forward(self, key, delay=DEFAULT_DELAY, resume_count=None):
        source = FORWARD_SOURCES.get(key)
        if not source:
            raise RuntimeError(f"No forward source configured for {key}")
        if key in self.runners and not self.runners[key].task.done():
            raise RuntimeError(f"{key} is already running")
        media = []
        async for msg in self.client.get_chat_history(source):
            if msg.media:
                media.append(int(msg.id))
        media.reverse()
        start = int(resume_count or 0)
        if start >= len(media):
            raise RuntimeError(f"Resume index {start} is at/after the end ({len(media)})")
        self._state.update({"source": key, "mode": "forward", "current_index": start, "delay": delay, "running": True})
        self._save()
        task = asyncio.create_task(self._forward_worker(key, source, media, start, delay))
        self.runners[key] = Runner(task, key, "forward")

    async def _forward_worker(self, key, source, media, start, delay):
        try:
            for i in range(start, len(media)):
                await self.client.forward_messages(self.runtime.adding_chat_id, source, media[i])
                self._state.update({"source": key, "current_index": i + 1, "running": True})
                self._save()
                await asyncio.sleep(delay)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            self._state["last_error"] = str(exc)
            log.exception("forward helper failed: %s", key)
        finally:
            self._state["running"] = False
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
        return (
            "🛠 <b>HELPER STATUS</b>\n"
            f"Running: <code>{'YES' if running else 'NO'}</code>\n"
            f"Jobs: <code>{', '.join(running) or '-'}</code>\n"
            f"Mode: <code>{self._state.get('mode', '-')}</code>\n"
            f"Source: <code>{self._state.get('source', '-')}</code>\n"
            f"Index: <code>{self._state.get('current_index', 0)}</code>\n"
            f"Delay: <code>{self._state.get('delay', DEFAULT_DELAY)}s</code>\n"
            f"Last error: <code>{self._state.get('last_error', '-')}</code>"
        )

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
                    await self.start_inline(key, delay, count or 0)
                    await message.reply(f"Resumed {key}.\\nCount: {count or 0}\\nDelay: {delay}s")
                else:
                    await self.start_inline(key, delay)
                    await message.reply(f"Started {key}.\\nSource: {SOURCES[key][0]}\\nDelay: {delay}s")
            except Exception as exc:
                await message.reply(f"Helper error: {exc}")
            return True
        for key, source in FORWARD_SOURCES.items():
            starts = (f"/startfw{key}bot", f"/startfw{key}")
            resumes = (f"/resumefw{key}bot", f"/resumefw{key}")
            if cmd in starts or cmd in resumes:
                try:
                    if cmd in resumes:
                        count, delay = self._resume_args(text)
                    else:
                        count, delay = None, self._start_delay(text)
                    await self.start_forward(key, delay, count if cmd in resumes else None)
                    await message.reply(f"{'Resumed' if cmd in resumes else 'Started'} forward {key}. Delay: {delay}s")
                except Exception as exc:
                    await message.reply(f"Forward helper error: {exc}")
                return True
        return False

    def help_text(self):
        return (
            "AddHelper ready ✅\n\n"
            "/startcatchbot [delay]\n"
            "/resumecatchbot &lt;count&gt; [delay]\n"
            "/starthallowbot [delay]\n"
            "/resumehallowbot &lt;count&gt; [delay]\n"
            "/startcapturebot [delay]\n"
            "/resumecapturebot &lt;count&gt; [delay]\n"
            "/startseizerbot [delay]\n"
            "/resumeseizerbot &lt;count&gt; [delay]\n"
            "/startgrabbot [delay]\n"
            "/resumegrabbot &lt;count&gt; [delay]\n"
            "/starttakersbot [delay]\n"
            "/resumetakersbot &lt;count&gt; [delay]\n"
            "/startpickerbot [delay]\n"
            "/resumepickerbot &lt;count&gt; [delay]\n"
            "/startzicekobot [delay]\n"
            "/resumezicekobot &lt;count&gt; [delay]\n"
            "/startorinbot [delay]\n"
            "/resumeorinbot &lt;count&gt; [delay]\n"
            "/startdaobot [delay]\n"
            "/resumedaobot &lt;count&gt; [delay]\n\n"
            "Controls: /helperstatus /stophelper /resethelperprogress"
        )
