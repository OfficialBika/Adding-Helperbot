from dataclasses import dataclass
from datetime import datetime


@dataclass
class LookupMediaRecord:
    """Minimal media data prepared for external lookup bots."""

    lookup_key: str
    file_id: str
    media_type: str
    created_at: datetime = datetime.utcnow()


class LookupExportService:
    """Exports only lookup-required data.

    Original media binaries are not stored here.
    This layer keeps only references required by lookup services.
    """

    def build_record(self, media):
        return LookupMediaRecord(
            lookup_key=media.file_unique_id,
            file_id=media.file_id,
            media_type=media.media_type,
        )


lookup_export_service = LookupExportService()
