
from .client import create_helper_client
from .watcher import ResponseWatcher, build_source_resolver
from .config import SOURCES

class HelperRuntime:
    def __init__(self):
        self.client=None
        self.controller=None
        self.watcher=ResponseWatcher()

    async def start(self, controller):
        self.controller=controller
        self.client=create_helper_client()
        if self.client:
            self.watcher.bind_client(self.client, build_source_resolver(SOURCES))
            await self.client.start()
        return self.client

    async def stop(self):
        if self.client:
            await self.client.stop()
            self.client=None
