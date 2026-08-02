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


items_repo = ItemRepository()
users_repo = UserRepository()
