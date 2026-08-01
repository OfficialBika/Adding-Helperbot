from dataclasses import dataclass
from datetime import datetime


@dataclass
class ThumbnailMetadata:
    media_id: str
    thumbnail_id: str
    created_at: datetime = datetime.utcnow()


class ThumbnailCacheService:
    """Fast thumbnail reference cache for image and video previews."""

    def __init__(self):
        self.cache = {}

    def save(self, metadata: ThumbnailMetadata):
        self.cache[metadata.media_id] = metadata

    def get(self, media_id: str):
        return self.cache.get(media_id)


thumbnail_cache_service = ThumbnailCacheService()
