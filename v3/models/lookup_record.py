from dataclasses import dataclass, field
from datetime import datetime
from typing import Any


@dataclass
class LookupRecord:
    """Normalized document written for lookup bots."""

    name: str
    file_id: str
    file_unique_id: str
    source_bot: str
    collection: str
    media_type: str = "unknown"
    tags: list[str] = field(default_factory=list)
    metadata: dict[str, Any] = field(default_factory=dict)
    created_at: datetime = field(default_factory=datetime.utcnow)
