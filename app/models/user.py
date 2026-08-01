from dataclasses import dataclass
from datetime import datetime


@dataclass
class UserRecord:
    user_id: int
    username: str | None = None
    created_at: datetime = datetime.utcnow()
