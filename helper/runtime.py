from .client import create_helper_client

class HelperRuntime:
    def __init__(self):
        self.client = None
        self.controller = None

    async def start(self, controller):
        self.controller = controller
        self.client = create_helper_client()
        if self.client:
            await self.client.start()
        return self.client

    async def stop(self):
        if self.client:
            await self.client.stop()
            self.client = None
