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
        if source_key not in SOURCES:
            raise ValueError(f"Unknown helper source: {source_key}")
        await self.jobs.create(source_key, start_id)
        if not client:
            return
        source = SOURCES[source_key]
        task = asyncio.create_task(CommandCrawler(
            client, source, self.watcher,
            HelperForwarder(target_chat), self.jobs
        ).run(start_id))
        self.tasks[source_key] = task
        self.dm.add(source_key, task)
        return self.jobs.get(source_key)

    async def resume(self, source_key, start_id=None, client=None, target_chat=None):
        return await self.start(source_key, start_id or 1, client, target_chat)

    async def stop_all_dm(self):
        await self.dm.stop_all()

    async def stop(self, source_key):
        self.dm.stop(source_key)
        await self.jobs.stop(source_key)
