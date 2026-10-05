from __future__ import annotations

import re
import unicodedata


LABEL_ALIASES = {
    "name": r"(?:character\s*name|char\s*name|character|name)",
    "anime": r"(?:anime|series|movie)",
    "id": r"(?:character\s*)?id|item\s*id|card\s*id",
    "rarity": r"rarity",
    "role": r"role",
}

NOISE_RE = re.compile(
    r"(?:new\s+(?:character|waifu|husbando)\s+added|"
    r"added\s+new\s+character|"
    r"uploaded\s*\(/?li\)|"
    r"artwork\s+updated|rarity\s+updated|role\s+updated|"
    r"character\s+updated|global\s+owners|globally\s+catches|"
    r"added\s+by|uploader|photo\s+updated|leave\s+a\s+comment|"
    r"comments?\b)",
    re.I,
)


def norm(text: str | None) -> str:
    text = unicodedata.normalize("NFKC", text or "")
    text = text.replace("\r", "\n")
    text = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", text)
    return re.sub(r"[ \t]+", " ", text).strip()


def strip_symbols(value: str) -> str:
    value = value.strip()
    value = re.sub(r"^[^\w\u00c0-\u024f\u0400-\u04ff\u3040-\u30ff\u4e00-\u9fff\uac00-\ud7af]+", "", value)
    # Do not strip closing brackets from legitimate name suffixes such as
    # "Yoru [🪶]". Only remove separator characters around the whole value.
    return value.strip(" |•:：-–—")


def clean_name(value: str) -> str:
    value = norm(value)
    # Telegram source bots may wrap field values in Markdown code ticks.
    # The ticks are formatting only and must never become part of the stored name.
    value = re.sub(r"^\s*`+(.*?)`+\s*$", r"\1", value, flags=re.S).strip()
    value = re.sub(r"^(?:📛|👤|🆔|⭐|💠|🎬|🎭|📤)+\s*", "", value)
    value = re.sub(r"^(?:name|character\s*name|char\s*name)\s*[:：•\-=]\s*", "", value, flags=re.I)
    value = re.split(
        r"\s*(?:\||•)\s*(?:anime|movie|series|rarity|role|id)\b",
        value,
        maxsplit=1,
        flags=re.I,
    )[0]
    value = re.sub(r"\s*[-–—|]+\s*(?:rarity|anime|id|role)\b.*$", "", value, flags=re.I)
    value = strip_symbols(value)
    return re.sub(r"\s+", " ", value).strip() or None


def _label_value(text: str, label: str) -> str | None:
    pat = re.compile(
        rf"(?:^|[\n\r\s])[^\w\n\r:：•\-=]{{0,8}}{label}\s*[:：•\-=]\s*(.+?)"
        rf"(?=\s+[^\w\n\r:：•\-=]{{0,8}}(?:{LABEL_ALIASES['id']}|{LABEL_ALIASES['name']}|{LABEL_ALIASES['anime']}|{LABEL_ALIASES['rarity']}|{LABEL_ALIASES['role']})\s*[:：•\-=]|$)",
        re.I | re.S,
    )
    m = pat.search(text)
    return clean_name(m.group(1)) if m else None


def _line_label_value(line: str, label: str) -> str | None:
    m = re.search(rf"(?:[^\w\n\r:：•\-=]{{0,8}}){label}\s*[:：•\-=]\s*(.+?)\s*$", line, re.I)
    return clean_name(m.group(1)) if m else None


def _myanmar_name(text: str) -> str | None:
    for line in norm(text).splitlines():
        line = line.strip()
        if not line:
            continue
        v = _line_label_value(line, r"(?:📛\s*)?Name")
        if v:
            return v
    for line in norm(text).splitlines():
        line = line.strip()
        if not line or NOISE_RE.search(line):
            continue
        if re.match(r"^📛\s*.+", line):
            return clean_name(line)
    return None


def _catch_log_name(text: str) -> str | None:
    """Parse Character_Catcher_Logs event captions.

    The log channel emits several caption shapes for the same character:
    changed-name events, image updates, event updates, and normal
    "added new Character" cards. Only the character name is returned.
    """
    raw = norm(text)
    if not raw:
        return None

    # Name-change event: prefer the New Name field over the old name.
    m = re.search(
        r"(?:^|\n)\s*New\s+Name\s*[:：]\s*(.+?)\s*(?:\n|$)",
        raw,
        re.I,
    )
    if m:
        value = clean_name(m.group(1))
        if value:
            return value

    # Image/event update captions: "... for Character Nicole Demara [emoji]".
    for label in (r"changed\s+event\s+for", r"updated\s+image\s+for"):
        m = re.search(
            rf"\b{label}\s+Character\s+(.+?)(?:\n|$)",
            raw,
            re.I,
        )
        if m:
            # Bracketed suffixes are part of the character name, not noise.
            # Example: "Rock Lee [👘]" must remain exactly "Rock Lee [👘]".
            value = clean_name(m.group(1))
            if value:
                return value

    # Some log captions say "added new Character (Video)" and put the
    # actual character name in a following "Character Name:" field. The
    # parenthesized media type is metadata, not the character name.
    m = re.search(
        r"\badded\s+new\s+Character[ \t]+(.+?)(?:\n|$)",
        raw,
        re.I,
    )
    if m:
        value = clean_name(m.group(1))
        if value and not re.fullmatch(
            r"\((?:video|photo|animation|document|media)\)",
            value,
            re.I,
        ):
            return value

    # If the event header contains only the media type, let the normal
    # Character Name parser below extract the real name from the labeled field.
    return None


def _picker_name(text: str) -> str | None:
    """Parse Picker Database OwO captions in both character/update formats."""
    raw = norm(text)
    if not raw or not re.search(
        r"owo!\s*check\s+out\s+this\s+(?:character|update)", raw, re.I
    ):
        return None

    for line in raw.splitlines():
        line = line.strip()

        # Character format:
        # 🆔️30: Ayaka
        m = re.match(
            r"^\s*[「『【\[\(]?\s*(?:🆔\ufe0f?\s*)?(\d+)\s*[:：-]\s*(.+)\s*$",
            line,
            re.I,
        )
        if m:
            value = clean_name(m.group(2))
            if value:
                return value

        # Update format:
        # 「 ID : 2601 Shanks ⛓️ 」
        m = re.match(
            r"^\s*[「『【\[\(]?\s*ID\s*[:：-]\s*(\d+)\s+(.+)\s*$",
            line,
            re.I,
        )
        if m:
            value = clean_name(m.group(2))
            if value:
                return value

    return None


def _picker_id(text: str) -> str | None:
    """Parse the numeric ID from Picker Database OwO captions."""
    raw = norm(text)
    if not raw or not re.search(
        r"owo!\s*check\s+out\s+this\s+(?:character|update)", raw, re.I
    ):
        return None

    for line in raw.splitlines():
        line = line.strip()

        # Character format: 🆔️30: Ayaka
        m = re.match(
            r"^\s*[「『【\[\(]?\s*(?:🆔\ufe0f?\s*)?(\d+)\s*[:：-]",
            line,
            re.I,
        )
        if m:
            return m.group(1)

        # Update format: 「 ID : 2601 Shanks ⛓️ 」
        m = re.match(
            r"^\s*[「『【\[\(]?\s*ID\s*[:：-]\s*(\d+)(?:\s|$)",
            line,
            re.I,
        )
        if m:
            return m.group(1)

    return None


def _waifux_global_id(text: str) -> str | None:
    """Parse WaifuxGrabBot Global Character Info ID field.

    Waifux uses a bullet-prefixed field such as:
        • ID: 3

    The generic ID parser excludes the bullet separator, so this
    source-specific parser runs first to make the source ID authoritative.
    """
    raw = norm(text)
    if not raw or not re.search(r"global\s+character\s+info", raw, re.I):
        return None

    for line in raw.splitlines():
        line = line.strip()
        m = re.match(
            r"^[•●▪️🔹🔸\-\*–—]?\s*(?:🆔\ufe0f?\s*)?(?:character\s*)?id\s*[:：=-]\s*`?(\d+)`?\s*$",
            line,
            re.I,
        )
        if m:
            return m.group(1)
    return None

def _capture_name(text: str) -> str | None:
    """Parse CaptureCharacterBot's New Character Added card."""
    raw = norm(text)
    if not raw or not re.search(r"new\s+character\s+added", raw, re.I):
        return None
    for line in raw.splitlines():
        m = re.match(r"^\s*🎭\s*Name\s*[:：]?\s*(.+?)\s*$", line, re.I)
        if m:
            value = clean_name(m.group(1))
            if value:
                return value
    return None


def _capture_id(text: str) -> str | None:
    """Parse CaptureCharacterBot's numeric ID field only."""
    raw = norm(text)
    if not raw or not re.search(r"new\s+character\s+added", raw, re.I):
        return None
    for line in raw.splitlines():
        m = re.match(r"^\s*🆔(?:\ufe0f)?\s*ID\s*[:：-]?\s*(\d+)\s*$", line, re.I)
        if m:
            return m.group(1)
    return None


def _kairo_name(text: str) -> str | None:
    """Parse KairoCollectBot's New Card Added caption."""
    raw = norm(text)
    if not raw or not re.search(r"new\s+card\s+added", raw, re.I):
        return None
    for line in raw.splitlines():
        m = re.search(r"^\s*[📛]?\s*Character\s*[:：]\s*(.+?)\s*$", line, re.I)
        if m:
            value = clean_name(m.group(1))
            if value:
                return value
    return None


def _catch_your_waifu_name(text: str) -> str | None:
    """Parse Catch_Your_Waifu_Bot's /w Character Details card."""
    raw = norm(text)
    if not raw:
        return None
    for line in raw.splitlines():
        line = line.strip()
        match = re.match(r"^[•●▪️🔹🔸]\s*(?:Name|Character\s*Name)\s*[:：]\s*(.+?)\s*$", line, re.I)
        if match:
            value = clean_name(match.group(1))
            if value:
                return value
    return None


def _senpai_name(text: str) -> str | None:
    for line in norm(text).splitlines():
        v = _line_label_value(line, r"(?:👤\s*)?NAME")
        if v:
            return v.upper() if re.search(r"[A-Za-z]", v) else v
    return None


def _senpai_inline_name(text: str) -> str | None:
    """Parse Senpai media cards in both raw and forwarded forms."""
    for line in norm(text).splitlines():
        m = re.match(
            r"^\s*(?:media\s*\+\s*)?🎴\s*(.+?)\s*\|\s*(.+?)\s*$",
            line,
            re.I,
        )
        if m:
            value = clean_name(m.group(1))
            if value and not re.match(r"^(?:⚖️\s*)?character\s+valuation$", value, re.I):
                return value

        # Fallback if the card emoji is omitted but Name | Rarity remains.
        m = re.match(
            r"^\s*(?:media\s*\+\s*)?[^\w\n\r]{1,4}(.+?)\s*\|\s*(.+?)\s*$",
            line,
            re.I,
        )
        if m and not re.search(r"^character\s+valuation$", m.group(1).strip(), re.I):
            value = clean_name(m.group(1))
            if value:
                return value
    return None

def _waifux_global_name(text: str) -> str | None:
    """Parse WaifuxGrabBot's Global Character Info card.

    Example::
        ➤ Tsunade Senju 🟠
        • Series: Naruto/Boruto
        • ID: 1

    Only the character name is returned. Trailing rarity/status emoji are
    treated as card metadata and are never persisted as part of the name.
    """
    raw = norm(text)
    if not raw or not re.search(r"global\s+character\s+info", raw, re.I):
        return None

    for line in raw.splitlines():
        line = line.strip()
        m = re.match(r"^➤\s*(.+?)\s*$", line)
        if not m:
            continue

        value = m.group(1).strip()
        # Waifux puts rarity/status emoji at the end of this line, e.g. 🟠.
        # Remove only trailing Unicode symbol/modifier characters, leaving
        # normal punctuation inside a character name untouched.
        while value:
            last = value[-1]
            if last in "\ufe0f\u200d\u20e3" or unicodedata.category(last) in {"So", "Sk"}:
                value = value[:-1].rstrip()
                continue
            break

        value = clean_name(value)
        if value:
            return value
    return None


def _smash_name(text: str) -> str | None:
    raw = norm(text)
    m = re.search(
        r"look\s+at\s+this\s+character\s*(?:\n|\s)+(.+?)\s+from\s+(.+?)(?:!|！|\n|$)",
        raw,
        re.I | re.S,
    )
    if m:
        return clean_name(m.group(1))
    for line in raw.splitlines():
        m = re.match(r"^(.+?)\s+from\s+(.+?)(?:!|！)?$", line.strip(), re.I)
        if m:
            return clean_name(m.group(1))
    return None


def extract_character_id(text: str | None) -> str | None:
    """Return the source character ID when the source format exposes one."""
    raw = norm(text)
    if not raw:
        return None

    waifux_id = _waifux_global_id(raw)
    if waifux_id:
        return waifux_id

    # Picker Database exposes two OwO ID layouts:
    #   🆔️30: Ayaka
    #   「 ID : 2601 Shanks ⛓️ 」
    capture_id = _capture_id(raw)
    if capture_id:
        return capture_id

    picker_id = _picker_id(raw)
    if picker_id:
        return picker_id

    # Kairo may wrap the numeric ID in Markdown code ticks, e.g. ID: 3.
    # Formatting ticks are never part of the stored ID.
    if re.search(r"new\s+card\s+added", raw, re.I):
        for line in raw.splitlines():
            m = re.match(
                r"^\s*[^\w\n\r:：•\-=]{0,8}ID\s*[:：\-]\s*`?(\d+)`?\s*$",
                line,
                re.I,
            )
            if m:
                return m.group(1)

    # Group the complete ID-label alternation so the delimiter applies
    # to every supported label form.
    id_label = rf"(?:{LABEL_ALIASES['id']})"
    for line in raw.splitlines():
        line = line.strip()
        m = re.match(
            rf"^\s*[^\w\n\r:：•\-=]{{0,8}}{id_label}\s*[:：•\-=]\s*(\d+)\s*$",
            line,
            re.I,
        )
        if m:
            return m.group(1)

    # Senpai commonly renders this as "🆔 ID: 4". Telegram clients may
    # preserve an optional variation selector after the emoji, so accept it.
    for line in raw.splitlines():
        line = line.strip()
        m = re.match(
            r"^[🆔🔢#](?:\ufe0f)?\s*(?:ID\s*)?[:：-]\s*(\d+)\s*$",
            line,
            re.I,
        )
        if m:
            return m.group(1)

    # Explicit textual ID forms, including an emoji prefix.
    for line in raw.splitlines():
        line = line.strip()
        m = re.match(
            r"^[^\w\n\r:：•\-=]{0,8}\s*(?:character\s*)?id\s*[:：•\-=]\s*(\d+)\s*$",
            line,
            re.I,
        )
        if m:
            return m.group(1)

    # Character Catcher/OwO format:
    # OwO! Check out this character!
    #
    # Anime
    # 35: Character Name [emoji]
    # (rarity)
    # The previous implementation incorrectly required the internal
    # "media + owo!" phrase, which is not present in the actual caption.
    if re.search(r"owo!\s*check\s+out\s+this\s+(?:character|waifu)", raw, re.I):
        for line in raw.splitlines():
            m = re.match(r"^\s*(\d+)\s*[:：-]\s*.+?\s*$", line)
            if m:
                return m.group(1)

    for line in raw.splitlines():
        m = re.match(r"^\s*(\d+)\s*/\s*[^/]+(?:/|$)", line)
        if m:
            return m.group(1)

    return None


def extract_name(text: str | None) -> str | None:
    raw = norm(text)
    if not raw:
        return None

    for parser in (_capture_name, _picker_name, _kairo_name, _catch_your_waifu_name, _waifux_global_name, _catch_log_name, _senpai_inline_name, _senpai_name, _myanmar_name, _smash_name):
        name = parser(raw)
        if name:
            return name

    for line in raw.splitlines():
        for label in (
            LABEL_ALIASES["name"],
            r"(?:📛\s*)?Name",
            r"(?:👤\s*)?NAME",
        ):
            value = _line_label_value(line, label)
            if value:
                return value

    value = _label_value(raw, LABEL_ALIASES["name"])
    if value:
        return value

    if re.search(r"owo!\s*check\s+out\s+this\s+(?:character|waifu)", raw, re.I):
        for line in raw.splitlines():
            line = line.strip()
            m = re.match(r"^(?:ID\s*)?(\d+)\s*[:：-]\s*(.+?)\s*$", line, re.I)
            if not m:
                continue
            # Bracketed emoji suffixes are part of the character name.
            # Example: "Yoru [👶]" must stay exactly "Yoru [👶]".
            value = clean_name(m.group(2))
            if value and not re.match(r"^(?:anime|rarity|id|role)\b", value, re.I):
                return value

    for line in raw.splitlines():
        line = line.strip()
        m = re.match(r"^(?:ID\s*)?(\d+)\s*[:：\-]\s*(.+?)\s*$", line, re.I)
        if m:
            value = clean_name(m.group(2))
            if value and not re.match(r"^(?:anime|rarity|id|role)\b", value, re.I):
                return value

        m = re.match(r"^(?:ID\s*)?(\d+)\s+(.+?)\s*$", line, re.I)
        if m:
            value = clean_name(m.group(2))
            if value and not NOISE_RE.search(value):
                return value

    for line in raw.splitlines():
        parts = [p.strip() for p in line.split("/")]
        if len(parts) >= 2 and parts[0].isdigit():
            value = clean_name(parts[1])
            if value:
                return value

    for line in raw.splitlines():
        m = re.match(r"^\s*(?:📛\s*)?name\s*[-–—:]\s*(.+)$", line, re.I)
        if m:
            value = clean_name(m.group(1))
            if value:
                return value

    return None



def extract_anime(text: str | None) -> str | None:
    """Extract an explicit Anime/Series/Movie field without altering bracketed suffixes."""
    raw = norm(text)
    if not raw:
        return None
    for line in raw.splitlines():
        value = _line_label_value(line, LABEL_ALIASES["anime"])
        if value:
            return value
    return None


def extract_rarity(text: str | None) -> str | None:
    """Extract an explicit rarity field or Senpai's `Name | Rarity` card suffix."""
    raw = norm(text)
    if not raw:
        return None
    for line in raw.splitlines():
        value = _line_label_value(line, LABEL_ALIASES["rarity"])
        if value:
            return value
        m = re.match(
            r"^\s*(?:media\s*\+\s*)?(?:🎴\s*)?.+?\s*\|\s*(.+?)\s*$",
            line,
            re.I,
        )
        if m:
            candidate = clean_name(m.group(1))
            if candidate and not re.search(r"^character\s+valuation$", candidate, re.I):
                return candidate
    return None
