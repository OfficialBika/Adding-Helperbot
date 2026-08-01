from dataclasses import dataclass
from datetime import datetime


@dataclass
class MediaMetadata:
    file_id: str
    unique_id: str
    media_type: str
    file_size: int = 0
    width: int | None = None
    height: int | None = None
    duration: int | None = None
    created_at: datetime = datetime.utcnow()


class MediaStorageService:
    """High performance media metadata storage layer.

    Keeps Telegram file references instead of unnecessary binary duplication.
    """

    def build_metadata(self, media):
        return MediaMetadata(
            file_id=media.file_id,
            unique_id=media.file_unique_id,
            media_type=media.type,
            file_size=getattr(media, "file_size", 0),
            width=getattr(media, "width", None),
            height=getattr(media, "height", None),
            duration=getattr(media, "duration", None),
        )


media_storage_service = MediaStorageService()
