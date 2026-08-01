from aiogram import Dispatcher

from app.handlers.start import router as start_router
from app.handlers.image_handler import router as image_router


def register_handlers(dp: Dispatcher):
    dp.include_router(start_router)
    dp.include_router(image_router)
