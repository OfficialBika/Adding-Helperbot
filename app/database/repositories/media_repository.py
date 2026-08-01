from datetime import datetime


class MediaRepository:
    """Repository layer for optimized image and video metadata storage."""

    def __init__(self, collection=None):
        self.collection = collection

    async def save(self, metadata):
        if self.collection is None:
            return None

        document = {
            "file_id": metadata.file_id,
            "unique_id": metadata.unique_id,
            "media_type": metadata.media_type,
            "file_size": metadata.file_size,
            "width": metadata.width,
            "height": metadata.height,
            "duration": metadata.duration,
            "created_at": datetime.utcnow(),
        }

        return await self.collection.insert_one(document)

    async def find_by_unique_id(self, unique_id):
        if self.collection is None:
            return None

        return await self.collection.find_one({"unique_id": unique_id})


media_repository = MediaRepository()
