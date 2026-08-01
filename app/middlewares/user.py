from aiogram import BaseMiddleware

from app.services.user_service import user_service


class UserMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        user = data.get("event_from_user")
        if user:
            await user_service.register(user)
        return await handler(event, data)


user_middleware = UserMiddleware()
