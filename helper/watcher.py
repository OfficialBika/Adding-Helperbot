
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
            key = source_resolver(message) if source_resolver else None
            if key:
                await self.push(key, message)


def build_source_resolver(sources):
    def resolve(message):
        username = ""
        if getattr(message, "from_user", None):
            username = (message.from_user.username or "").lower()
        for key, source in sources.items():
            bot_name = getattr(source, "bot", "")
            if isinstance(source, dict):
                bot_name = source.get("bot", "")
            bot_name = str(bot_name).replace("@", "").lower()
            if bot_name and bot_name == username:
                return key
        return None
    return resolve
