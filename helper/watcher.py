
import asyncio
from collections import defaultdict

class ResponseWatcher:
    def __init__(self, timeout=30):
        self.timeout = timeout
        self.queues = defaultdict(asyncio.Queue)

    async def push(self, source_key, message):
        await self.queues[source_key].put(message)

    async def wait(self, source_key):
        try:
            return await asyncio.wait_for(
                self.queues[source_key].get(),
                timeout=self.timeout
            )
        except asyncio.TimeoutError:
            return None

    def bind_client(self, client, source_resolver=None):
        if not client:
            return

        @client.on_message()
        async def _handler(_, message):
            if not message.from_user:
                return
            key = source_resolver(message) if source_resolver else None
            if key:
                await self.push(key, message)
