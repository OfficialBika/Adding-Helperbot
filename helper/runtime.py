from .client import create_helper_client
from .watcher import build_source_resolver, ResponseWatcher
from .config import SOURCES

class HelperRuntime:
    def __init__(self):
        self.client = None
        self.controller = None
        self.watcher = None

    async def start(self, controller):
        self.controller = controller
        self.client = create_helper_client()
        if self.client:
            # Use controller watcher as the single source of truth
            self.watcher = controller.watcher
            self.watcher.bind_client(
                self.client,
                build_source_resolver(SOURCES)
            )
            await self.client.start()
        return self.client

    async def stop(self):
        if self.client:
            await self.client.stop()
            self.client = None
