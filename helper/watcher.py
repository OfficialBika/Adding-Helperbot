import asyncio

class ResponseWatcher:
    def __init__(self, timeout=30):
        self.timeout=timeout

    async def wait(self, event_queue):
        try:
            return await asyncio.wait_for(event_queue.get(), self.timeout)
        except asyncio.TimeoutError:
            return None
