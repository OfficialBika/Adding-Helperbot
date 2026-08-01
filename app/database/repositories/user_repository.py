class UserRepository:
    def __init__(self, database=None):
        self.database = database

    async def save(self, data: dict):
        if self.database and self.database.db:
            return await self.database.db.users.update_one(
                {"user_id": data["user_id"]},
                {"$set": data},
                upsert=True,
            )
        return None


user_repository = UserRepository()
