from aiogram import BaseMiddleware


class ErrorMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        try:
            return await handler(event, data)
        except Exception as error:
            print(f"Handler error: {error}")
            return None


error_middleware = ErrorMiddleware()
