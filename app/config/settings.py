import os
from dotenv import load_dotenv

load_dotenv()

class Settings:
    BOT_TOKEN = os.getenv("BOT_TOKEN", "")
    DATABASE_URL = os.getenv("DATABASE_URL", "")

settings = Settings()
