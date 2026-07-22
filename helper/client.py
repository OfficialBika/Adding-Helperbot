from pyrogram import Client
from .config import API_ID, API_HASH, SESSION_STRING

def create_helper_client():
    if not API_ID or not API_HASH or not SESSION_STRING:
        return None
    return Client(
        "adding_helper",
        api_id=API_ID,
        api_hash=API_HASH,
        session_string=SESSION_STRING,
    )
