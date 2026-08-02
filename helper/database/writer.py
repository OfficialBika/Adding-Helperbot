from datetime import datetime


class MediaWriter:
    """Save media data for NameBotV3 lookup database."""

    def __init__(self, collection=None):
        self.collection = collection

    async def save(self, data: dict):
        if self.collection is None:
            return None

        file_unique_id = data.get("file_unique_id")

        if not file_unique_id:
            return await self.collection.insert_one(data)

        data["updated_at"] = datetime.utcnow()

        return await self.collection.update_one(
            {"file_unique_id": file_unique_id},
            {
                "$set": data,
                "$setOnInsert": {
                    "created_at": datetime.utcnow()
                },
            },
            upsert=True,
        )


media_writer = MediaWriter()
