from dataclasses import dataclass, field
from datetime import datetime, timezone

@dataclass
class HelperJob:
    source: str
    current_id: int
    status: str = "running"
    retry: int = 0
    updated_at: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
