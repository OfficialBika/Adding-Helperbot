from datetime import datetime

from v3.models.lookup_record import LookupRecord


class LookupNormalizer:
    """Convert parser output into a standard lookup document."""

    def normalize(self, parsed_data: dict, source_bot: str, collection: str):
        return LookupRecord(
            name=parsed_data.get("name", "unknown"),
            file_id=parsed_data.get("file_id", ""),
            file_unique_id=parsed_data.get("file_unique_id", ""),
            source_bot=source_bot,
            collection=collection,
            media_type=parsed_data.get("media_type", "unknown"),
            tags=parsed_data.get("tags", []),
            metadata={
                "raw": parsed_data.get("raw"),
            },
            created_at=datetime.utcnow(),
        )


lookup_normalizer = LookupNormalizer()
