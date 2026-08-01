from app.database.connection import database
from app.database.indexes import IMAGE_INDEXES, USER_INDEXES


class DatabaseService:
    async def initialize_indexes(self):
        if not database.db:
            return

        for index in IMAGE_INDEXES:
            await database.db.images.create_index(
                index["keys"],
                unique=index["unique"],
            )

        for index in USER_INDEXES:
            await database.db.users.create_index(
                index["keys"],
                unique=index["unique"],
            )


database_service = DatabaseService()
