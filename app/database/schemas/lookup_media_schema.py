from datetime import datetime


LOOKUP_MEDIA_SCHEMA = {
    "lookup_key": str,
    "file_id": str,
    "media_type": str,
    "tags": list,
    "created_at": datetime,
}


LOOKUP_INDEXES = [
    "lookup_key",
    "tags",
]
