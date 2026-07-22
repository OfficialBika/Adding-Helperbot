
from datetime import datetime, timezone

class JobManager:
    def __init__(self, collection=None):
        self.collection = collection
        self.jobs = {}
        self.tasks = {}

    async def create(self, source, start_id):
        data={"source":source,"current_id":int(start_id),"status":"running",
              "retry":0,"updated_at":datetime.now(timezone.utc)}
        self.jobs[source]=data
        if self.collection is not None:
            await self.collection.update_one({"source":source},{"$set":data},upsert=True)
        return data

    async def update(self, source, **kwargs):
        self.jobs.setdefault(source,{})
        self.jobs[source].update(kwargs)
        self.jobs[source]["updated_at"]=datetime.now(timezone.utc)
        if self.collection is not None:
            await self.collection.update_one({"source":source},{"$set":self.jobs[source]},upsert=True)

    async def stop(self, source):
        await self.update(source,status="paused")

    async def resume_jobs(self):
        if self.collection is None:
            return []
        return await self.collection.find({"status":"running"}).to_list(None)

    def get(self, source):
        return self.jobs.get(source)


    async def restore_running(self, starter):
        jobs = await self.resume_jobs()
        for job in jobs:
            await starter(job["source"], job["current_id"])
