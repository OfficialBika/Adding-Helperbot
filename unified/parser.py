from __future__ import annotations

import logging
from dataclasses import replace

from parsers import PARSERS
from parsers.base import ParsedCharacter, clean_name, norm

log = logging.getLogger("unified-parser")

MIN_CONFIDENCE = 0.70
SOURCE_BOOST = 0.055


def _combined_text(text: str | None) -> str:
    return norm(text)


def parse_candidates(
    text: str | None,
    *,
    source_key: str | None = None,
) -> list[ParsedCharacter]:
    raw = _combined_text(text)
    if not raw:
        return []

    candidates: list[ParsedCharacter] = []
    for parser in PARSERS:
        try:
            candidate = parser.parse(raw)
        except Exception:
            log.exception("parser failed name=%s", parser.name)
            continue
        if candidate is None or not candidate.is_valid:
            continue

        score = candidate.confidence
        if source_key and source_key in getattr(parser, "source_keys", frozenset()):
            score = min(1.0, score + SOURCE_BOOST)

        candidate = replace(candidate, confidence=score)
        if candidate.confidence >= MIN_CONFIDENCE:
            candidates.append(candidate)

    candidates.sort(
        key=lambda item: (
            item.confidence,
            len(item.matched_fields),
            PARSERS.index(next(p for p in PARSERS if p.name == item.parser)),
        ),
        reverse=True,
    )
    return candidates


def parse_message(
    text: str | None,
    *,
    source_key: str | None = None,
) -> ParsedCharacter | None:
    candidates = parse_candidates(text, source_key=source_key)
    return candidates[0] if candidates else None


def parser_names() -> tuple[str, ...]:
    return tuple(parser.name for parser in PARSERS)


def extract_name(text: str | None, *, source_key: str | None = None) -> str | None:
    result = parse_message(text, source_key=source_key)
    return clean_name(result.name) if result else None


def extract_character_id(text: str | None, *, source_key: str | None = None) -> str | None:
    result = parse_message(text, source_key=source_key)
    return result.character_id if result else None


def extract_anime(text: str | None, *, source_key: str | None = None) -> str | None:
    result = parse_message(text, source_key=source_key)
    return result.anime if result else None


def extract_rarity(text: str | None, *, source_key: str | None = None) -> str | None:
    result = parse_message(text, source_key=source_key)
    return result.rarity if result else None
