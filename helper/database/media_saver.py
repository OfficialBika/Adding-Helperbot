from helper.database.schema import build_media_record
from helper.database.writer import media_writer
from helper.media.extractor import extract_media


async def save_media(message, name, source_bot, command=""):
    """Convert Telegram media into lookup data and save it."""

    media = extract_media(message)

    record = build_media_record(
        name=name,
        file_id=media.get("file_id", ""),
        file_unique_id=media.get("file_unique_id", ""),
        media_type=media.get("media_type", "unknown"),
        source_bot=source_bot,
        command=command,
        extra=media.get("metadata", {}),
    )

    return await media_writer.save(record)
