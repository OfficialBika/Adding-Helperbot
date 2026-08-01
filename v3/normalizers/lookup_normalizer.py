from datetime import datetime

from v3.models.lookup_record import LookupRecord


class LookupNormalizer:
    """Convert parser output into original-compatible lookup schema."""

    def normalize(self, parsed_data: dict, source_bot: str, collection: str):
        return LookupRecord(
            name=parsed_data.get("name", "unknown"),
            file_id=parsed_data.get("file_id", ""),
            file_unique_id=parsed_data.get("file_unique_id", ""),
            source_bot=source_bot,
            collection=collection,

            # Parsed information
            anime_name=parsed_data.get("anime_name", ""),
            rarity=parsed_data.get("rarity", ""),
            card_id=parsed_data.get("card_id", ""),
            command_name=parsed_data.get("command_name", ""),
            source_key=parsed_data.get("source_key", source_bot),
            raw_text=parsed_data.get("raw_text", ""),

            # Media metadata
            media_type=parsed_data.get("media_type", "unknown"),
            sha256=parsed_data.get("sha256", ""),
            phash=parsed_data.get("phash", ""),
            frame_hashes=parsed_data.get("frame_hashes", []),
            media_geometry=parsed_data.get("media_geometry", {}),

            # Fingerprints
            photo_fingerprint=parsed_data.get("photo_fingerprint", {}),
            video_fingerprint=parsed_data.get("video_fingerprint", {}),
            fingerprint_version=parsed_data.get("fingerprint_version", ""),

            tags=parsed_data.get("tags", []),
            metadata={
                "raw": parsed_data.get("raw"),
            },
            created_at=datetime.utcnow(),
        )


lookup_normalizer = LookupNormalizer()
