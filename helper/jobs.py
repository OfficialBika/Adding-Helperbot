from datetime import datetime, timezone
import asyncio

class JobManager:
    def __init__(self, collection=None):
        self.collection = collection
        self.jobs = {}
        self.locks = {}

    def get(self, source):
        return self.jobs.get(source)

    def lock(self, source):
        return self.locks.setdefault(source, asyncio.Lock())

    async def create(self, source, start_id):
        data = {
            "source": source,
            "current_id": int(start_id),
            "status": "running",
            "retry": 0,
            "last_message_id": None,
            "updated_at": datetime.now(timezone.utc),
        }
        self.jobs[source] = data
        if self.collection:
            await self.collection.update_one(
                {"source": source},
                {"$set": data},
                upsert=True,
            )
        return data

    async def update(self, source, **kwargs):
        data = self.jobs.setdefault(source, {"source": source})
        data.update(kwargs)
        data["updated_at"] = datetime.now(timezone.utc)
        if self.collection:
            await self.collection.update_one(
                {"source": source},
                {"$set": data},
                upsert=True,
            )
        return data

    async def restore_running(self):
        if not self.collection:
            return list(self.jobs.values())
        result = []
        async for item in self.collection.find({"status": "running"}):
            self.jobs[item["source"]] = item
            result.append(item)
        return result

    async def stop(self, source):
        await self.update(source, status="paused")
