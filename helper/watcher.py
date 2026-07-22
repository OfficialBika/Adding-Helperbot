import asyncio
from collections import defaultdict

class ResponseWatcher:
    def __init__(self, timeout=30):
        self.timeout = timeout
        self._queues = defaultdict(asyncio.Queue)

    async def push(self, source_key, message):
        await self._queues[source_key].put(message)

    async def wait(self, source_key, check=None):
        try:
            while True:
                msg = await asyncio.wait_for(
                    self._queues[source_key].get(),
                    timeout=self.timeout
                )
                if check is None or check(msg):
                    return msg
        except asyncio.TimeoutError:
            return None
