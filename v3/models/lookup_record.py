from dataclasses import dataclass, field
from datetime import datetime
from typing import Any


@dataclass
class LookupRecord:
    """Normalized lookup document compatible with original media schema."""

    name: str
    file_id: str
    file_unique_id: str
    source_bot: str
    collection: str

    # Parsed information
    anime_name: str = ""
    rarity: str = ""
    card_id: str = ""
    command_name: str = ""
    source_key: str = ""
    raw_text: str = ""

    # Media information
    media_type: str = "unknown"
    sha256: str = ""
    phash: str = ""
    frame_hashes: list[str] = field(default_factory=list)
    media_geometry: dict[str, Any] = field(default_factory=dict)

    # Fingerprint compatibility
    photo_fingerprint: dict[str, Any] = field(default_factory=dict)
    video_fingerprint: dict[str, Any] = field(default_factory=dict)
    fingerprint_version: str = ""

    tags: list[str] = field(default_factory=list)
    metadata: dict[str, Any] = field(default_factory=dict)
    created_at: datetime = field(default_factory=datetime.utcnow)
