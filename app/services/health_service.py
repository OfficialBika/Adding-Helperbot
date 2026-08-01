from app.database.connection import database


class HealthService:
    async def check(self):
        return {
            "bot": True,
            "database": database.db is not None,
        }


health_service = HealthService()
