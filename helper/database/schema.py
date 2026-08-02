from datetime import datetime


def build_media_record(
    name: str,
    file_id: str,
    file_unique_id: str,
    media_type: str,
    source_bot: str,
    command: str = "",
    extra: dict | None = None,
):
    """Create MongoDB document format for NameBotV3 lookup data."""

    record = {
        "name": name,
        "file_id": file_id,
        "file_unique_id": file_unique_id,
        "media_type": media_type,
        "source_bot": source_bot,
        "command": command,
        "metadata": extra or {},
        "created_at": datetime.utcnow(),
        "updated_at": datetime.utcnow(),
    }

    return record
