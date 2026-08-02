"""Compatibility adapter while moving app.py to centralized config."""

from config import settings


BOT_TOKEN = settings.bot_token
MONGO_URI = settings.mongo_uri
DB_NAME = settings.db_name
OWNER_IDS = settings.owner_ids
LOG_LEVEL = settings.log_level
PORT = settings.port
USE_WEBHOOK = settings.use_webhook
