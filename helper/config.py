import os

API_ID = int(os.getenv("API_ID", "0") or 0)
API_HASH = os.getenv("API_HASH", "")
SESSION_STRING = os.getenv("SESSION_STRING", "")

TARGET_CHAT = os.getenv("HELPER_TARGET_CHAT", "")
