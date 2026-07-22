import asyncio
from .config import SOURCES
from .jobs import JobManager
from .crawler import CommandCrawler
from .forwarder import HelperForwarder
from .watcher import ResponseWatcher
from .dm_manager import DMManager

class HelperController:
    def __init__(self, collection=None):
        self.jobs = JobManager(collection)
        self.tasks = {}
        self.watcher = ResponseWatcher()
        self.dm = DMManager()

    def get_source(self, key):
        return SOURCES.get(key)

    async def start(self, source_key, start_id=1, client=None, target_chat=None):
        await self.jobs.create(source_key, start_id)
        if client is None:
            return self.jobs.get(source_key)

        source = SOURCES[source_key]
        crawler = CommandCrawler(
            client,
            source,
            self.watcher,
            HelperForwarder(target_chat),
            self.jobs,
        )
        task = asyncio.create_task(crawler.run(start_id))
        self.tasks[source_key] = task
        return self.jobs.get(source_key)

    async def resume(self, source_key, start_id=None, client=None, target_chat=None):
        job = self.jobs.get(source_key)
        if start_id is None and job:
            start_id = job.get("current_id", 1)
        return await self.start(
            source_key,
            start_id or 1,
            client,
            target_chat
        )

    async def stop(self, source_key):
        task = self.tasks.get(source_key)
        if task:
            task.cancel()
        await self.jobs.stop(source_key)
