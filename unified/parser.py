from __future__ import annotations

import logging
from dataclasses import replace

from parsers import PARSERS, PARSER_MAP
from parsers.base import ParsedCharacter, clean_name, norm
from helper.registry import parser_names_for_source

log = logging.getLogger("unified-parser")

MIN_CONFIDENCE = 0.70
SOURCE_BOOST = 0.055
PARSER_PREFERENCE_BOOST = 0.04


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

    preferred_names = parser_names_for_source(source_key)
    if preferred_names:
        preferred_parsers = tuple(
            PARSER_MAP[name] for name in preferred_names if name in PARSER_MAP
        )
        preferred = _parse_with_parsers(raw, preferred_parsers, source_key, ordered_preference=True)
        if preferred:
            return preferred

    return _parse_with_parsers(raw, PARSERS, source_key, ordered_preference=False)


def _parse_with_parsers(
    raw: str,
    parser_order,
    source_key: str | None,
    *,
    ordered_preference: bool,
) -> list[ParsedCharacter]:
    candidates: list[ParsedCharacter] = []
    preferred_names = tuple(
        parser.name for parser in parser_order
    )
    preferred_rank = {name: index for index, name in enumerate(preferred_names)}

    for parser in parser_order:
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

        rank = preferred_rank.get(parser.name)
        if rank is not None:
            score = min(1.0, score + max(0.0, PARSER_PREFERENCE_BOOST - rank * 0.0125))

        candidate = replace(candidate, confidence=score)
        if candidate.confidence >= MIN_CONFIDENCE:
            candidates.append(candidate)

    if ordered_preference:
        candidates.sort(
            key=lambda item: (
                preferred_rank.get(item.parser, 10_000),
                -item.confidence,
                -len(item.matched_fields),
            )
        )
    else:
        candidates.sort(
            key=lambda item: (
                item.confidence,
                len(item.matched_fields),
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
