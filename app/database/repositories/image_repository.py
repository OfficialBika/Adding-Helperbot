class ImageRepository:
    def __init__(self, database=None):
        self.database = database

    async def save(self, data: dict):
        if self.database and self.database.db:
            return await self.database.db.images.insert_one(data)
        return None


image_repository = ImageRepository()
