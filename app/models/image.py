from dataclasses import dataclass
from datetime import datetime


@dataclass
class ImageRecord:
    file_id: str
    hash_value: str
    created_at: datetime = datetime.utcnow()
