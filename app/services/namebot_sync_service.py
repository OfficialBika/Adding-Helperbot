from dataclasses import asdict


class NameBotSyncService:
    """Prepare lightweight records for NameBotV3 lookup storage."""

    def serialize_lookup_record(self, record):
        return asdict(record)

    async def sync(self, record, target=None):
        """Sync lookup-only data to external lookup storage.

        Media binaries are never transferred.
        """
        payload = self.serialize_lookup_record(record)

        if target is None:
            return payload

        return await target.insert_one(payload)


namebot_sync_service = NameBotSyncService()
