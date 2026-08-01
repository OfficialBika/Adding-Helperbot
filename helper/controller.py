import asyncio
from types import SimpleNamespace
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
        src = SOURCES.get(key)
        if not src:
            return None
        return SimpleNamespace(key=key, **src)

    def is_running(self, source_key):
        task = self.tasks.get(source_key)
        return bool(task and not task.done())

    async def start(self, source_key, start_id=1, client=None, target_chat=None):
        source = self.get_source(source_key)
        if not source:
            raise ValueError(f"Unknown helper source: {source_key}")

        if not client:
            raise RuntimeError("Pyrogram DM client is not running")

        if self.is_running(source_key):
            return self.jobs.get(source_key)

        await self.jobs.create(source_key, int(start_id))

        async def worker():
            await CommandCrawler(
                client,
                source,
                self.watcher,
                HelperForwarder(target_chat),
                self.jobs,
            ).run(int(start_id))

        task = asyncio.create_task(worker())
        self.tasks[source_key] = task
        self.dm.add(source_key, task)
        return self.jobs.get(source_key)

    async def resume(self, source_key, start_id=None, client=None, target_chat=None):
        return await self.start(source_key, start_id or 1, client, target_chat)

    async def stop_all_dm(self):
        await self.dm.stop_all()
        self.tasks.clear()

    async def stop(self, source_key):
        self.dm.stop(source_key)
        self.tasks.pop(source_key, None)
        await self.jobs.stop(source_key)
