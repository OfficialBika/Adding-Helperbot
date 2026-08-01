from app.database.repositories.user_repository import user_repository


class UserService:
    async def register(self, user):
        return await user_repository.save({
            "user_id": user.id,
            "username": user.username,
        })


user_service = UserService()
