
import asyncio
from .config import SOURCES
from .jobs import JobManager
from .crawler import CommandCrawler
from .forwarder import HelperForwarder
from .watcher import ResponseWatcher

class HelperController:
    def __init__(self):
        self.jobs = JobManager()
        self.tasks = {}

    async def start(self, source_key, start_id=1, client=None, target_chat=None):
        source = SOURCES[source_key]
        self.jobs.create(source_key, start_id)
        # client is supplied by the userbot integration layer
        if client is None:
            return self.jobs.get(source_key)

        crawler = CommandCrawler(
            client,
            source,
            ResponseWatcher(),
            HelperForwarder(target_chat),
        )
        task = asyncio.create_task(crawler.run(start_id))
        self.tasks[source_key] = task
        return self.jobs.get(source_key)

    async def resume(self, source_key, start_id, client=None, target_chat=None):
        return await self.start(source_key, start_id, client, target_chat)

    def stop(self, source_key):
        self.jobs.stop(source_key)
        task = self.tasks.get(source_key)
        if task:
            task.cancel()
