from datetime import datetime, timezone

class JobManager:
    def __init__(self, collection=None):
        self.collection = collection
        self.jobs = {}

    def get(self, source):
        return self.jobs.get(source)

    async def create(self, source, start_id):
        data = {
            "source": source,
            "current_id": int(start_id),
            "status": "running",
            "retry": 0,
            "updated_at": datetime.now(timezone.utc)
        }
        self.jobs[source] = data
        if self.collection:
            await self.collection.update_one(
                {"source": source},
                {"$set": data},
                upsert=True
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
                upsert=True
            )

    async def restore_running(self):
        if not self.collection:
            return list(self.jobs.values())
        cursor = self.collection.find({"status": "running"})
        result = []
        async for item in cursor:
            self.jobs[item["source"]] = item
            result.append(item)
        return result

    async def stop(self, source):
        await self.update(source, status="paused")
