from .collections import items, sudo_users, known_users, user_modes, settings


class ItemRepository:
    def __init__(self):
        self.collection = items

    async def find_one(self, query: dict):
        return await self.collection.find_one(query)

    async def insert(self, document: dict):
        return await self.collection.insert_one(document)

    async def update(self, query: dict, update: dict):
        return await self.collection.update_one(query, update)


class UserRepository:
    def __init__(self):
        self.sudo_users = sudo_users
        self.known_users = known_users
        self.user_modes = user_modes

    async def get_user(self, user_id: int):
        return await self.known_users.find_one({"user_id": user_id})

    async def create_user(self, data: dict):
        return await self.known_users.insert_one(data)

    async def update_user(self, user_id: int, data: dict):
        return await self.known_users.update_one(
            {"user_id": user_id},
            {"$set": data},
        )

    async def set_mode(self, user_id: int, mode: str):
        return await self.user_modes.update_one(
            {"user_id": user_id},
            {"$set": {"mode": mode}},
            upsert=True,
        )


items_repo = ItemRepository()
users_repo = UserRepository()
