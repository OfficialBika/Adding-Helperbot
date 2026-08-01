import os
from dotenv import load_dotenv

load_dotenv()


class Settings:
    BOT_TOKEN = os.getenv("BOT_TOKEN", "")
    DATABASE_URL = os.getenv("DATABASE_URL", "")
    API_ID = os.getenv("API_ID", "")
    API_HASH = os.getenv("API_HASH", "")
    ADMIN_IDS = os.getenv("ADMIN_IDS", "")


settings = Settings()
