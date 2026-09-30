from __future__ import annotations

import logging
import time
from dataclasses import dataclass

from aiogram import Bot
from aiogram.types import InlineKeyboardButton, InlineKeyboardMarkup

from unified.config import settings

log = logging.getLogger("force-join")

_ACTIVE_STATUSES = {"member", "administrator", "creator", "owner"}
_RESTRICTED = "restricted"


@dataclass(frozen=True)
class ForceJoinTarget:
    chat_id: str | int
    label: str
    join_url: str


@dataclass(frozen=True)
class VerificationResult:
    verified: bool
    missing: tuple[ForceJoinTarget, ...] = ()
    error: str = ""


def _parse_targets(raw: str) -> tuple[ForceJoinTarget, ...]:
    targets: list[ForceJoinTarget] = []
    for item in str(raw or "").split(","):
        item = item.strip()
        if not item:
            continue

        if "|" in item:
            raw_chat, raw_url = item.split("|", 1)
            chat_ref = raw_chat.strip()
            join_url = raw_url.strip()
        else:
            chat_ref = item
            join_url = ""

        if chat_ref.startswith("https://t.me/"):
            join_url = join_url or chat_ref
            chat_ref = "@" + chat_ref.rstrip("/").rsplit("/", 1)[-1]

        if not chat_ref:
            continue

        if not join_url and chat_ref.startswith("@"):
            join_url = "https://t.me/" + chat_ref.lstrip("@")

        if not join_url:
            log.warning(
                "FORCE_JOIN target %r has no join URL; use chat|https://t.me/... for private/numeric chats",
                chat_ref,
            )

        label = chat_ref if not chat_ref.lstrip("-").isdigit() else "Required Channel"
        targets.append(
            ForceJoinTarget(
                chat_id=int(chat_ref) if chat_ref.lstrip("-").isdigit() else chat_ref,
                label=label,
                join_url=join_url,
            )
        )
    return tuple(targets)


class ForceJoinService:
    def __init__(
        self,
        *,
        enabled: bool = False,
        channels: str = "",
        cache_ttl_seconds: int = 60,
        cache_max_users: int = 10000,
    ):
        self.enabled = bool(enabled)
        self.targets = _parse_targets(channels)
        self.cache_ttl = max(5, int(cache_ttl_seconds))
        self.cache_max_users = max(1000, int(cache_max_users))
        self._verified_until: dict[int, float] = {}

        if self.enabled and not self.targets:
            log.warning("FORCE_JOIN_ENABLED=true but FORCE_JOIN_CHANNELS is empty; check is inactive")
        elif self.enabled:
            log.info("Force Join enabled: %s target(s)", len(self.targets))

    @property
    def active(self) -> bool:
        return self.enabled and bool(self.targets)

    def _cache_get(self, user_id: int) -> bool:
        expires = self._verified_until.get(int(user_id), 0.0)
        if expires > time.monotonic():
            return True
        self._verified_until.pop(int(user_id), None)
        return False

    def _cache_put(self, user_id: int):
        user_id = int(user_id)
        self._verified_until[user_id] = time.monotonic() + self.cache_ttl
        if len(self._verified_until) > self.cache_max_users:
            cutoff = time.monotonic()
            old = [uid for uid, expiry in self._verified_until.items() if expiry <= cutoff]
            for uid in old:
                self._verified_until.pop(uid, None)
            while len(self._verified_until) > self.cache_max_users:
                self._verified_until.pop(next(iter(self._verified_until)))

    def invalidate(self, user_id: int):
        self._verified_until.pop(int(user_id), None)

    async def verify(self, bot: Bot, user_id: int) -> VerificationResult:
        if not self.active:
            return VerificationResult(True)

        user_id = int(user_id)
        if self._cache_get(user_id):
            return VerificationResult(True)

        missing: list[ForceJoinTarget] = []
        errors: list[str] = []

        for target in self.targets:
            try:
                member = await bot.get_chat_member(target.chat_id, user_id)
                status = str(getattr(member, "status", "") or "").lower()
                if status in _ACTIVE_STATUSES:
                    continue
                if status == _RESTRICTED and bool(getattr(member, "is_member", False)):
                    continue
                missing.append(target)
            except Exception as exc:
                errors.append(f"{target.label}: {exc}")
                log.warning(
                    "Force Join verification failed chat=%s user=%s error=%s",
                    target.chat_id,
                    user_id,
                    exc,
                )

        if errors:
            return VerificationResult(
                False,
                tuple(missing or self.targets),
                "Telegram membership verification is temporarily unavailable.",
            )

        if missing:
            return VerificationResult(False, tuple(missing))

        self._cache_put(user_id)
        return VerificationResult(True)

    def keyboard(self) -> InlineKeyboardMarkup:
        rows: list[list[InlineKeyboardButton]] = []
        for target in self.targets:
            if target.join_url:
                rows.append([
                    InlineKeyboardButton(
                        text=f"📢 Join {target.label}",
                        url=target.join_url,
                    )
                ])
        rows.append([
            InlineKeyboardButton(
                text="✅ Verify",
                callback_data="forcejoin:verify",
            )
        ])
        return InlineKeyboardMarkup(inline_keyboard=rows)

    def prompt(self) -> str:
        return (
            "🔒 <b>Verification Required</b>\n\n"
            "ဒီ Bot ကိုအသုံးပြုရန် အောက်ပါ Channel များကို Join လုပ်ပြီး "
            "<b>✅ Verify</b> ကိုနှိပ်ပါ။\n\n"
            "Join လုပ်ပြီးသားဖြစ်ရင် Verify ကို ထပ်နှိပ်နိုင်ပါတယ်။"
        )

    def success_text(self) -> str:
        return "✅ <b>Verification Successful</b>\n\nLookup ကို ဆက်လက်အသုံးပြုနိုင်ပါပြီ။"

    def status(self) -> dict:
        return {
            "enabled": self.enabled,
            "active": self.active,
            "targets": len(self.targets),
            "verified_cache_users": len(self._verified_until),
        }


force_join = ForceJoinService(
    enabled=settings.force_join_enabled,
    channels=settings.force_join_channels,
    cache_ttl_seconds=settings.force_join_cache_ttl_seconds,
    cache_max_users=settings.force_join_cache_max_users,
)
