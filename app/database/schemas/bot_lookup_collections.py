from datetime import datetime


BOT_LOOKUP_COLLECTIONS = {
    "image_bot": "image_lookup",
    "video_bot": "video_lookup",
    "anime_bot": "anime_lookup",
    "name_bot": "name_lookup",
}


BASE_LOOKUP_FIELDS = {
    "file_id": str,
    "file_unique_id": str,
    "media_type": str,
    "name": str,
    "tags": list,
    "created_at": datetime,
}


def get_collection(bot_name: str):
    return BOT_LOOKUP_COLLECTIONS.get(bot_name)
