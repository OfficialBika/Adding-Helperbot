from aiogram import Dispatcher

from app.handlers.start import router as start_router


def register_handlers(dp: Dispatcher):
    dp.include_router(start_router)
