import asyncio
from collections import defaultdict

class ResponseWatcher:
    def __init__(self, timeout=30):
        self.timeout = timeout
        self.queues = defaultdict(asyncio.Queue)
        self.seen_messages = set()

    async def push(self, source_key, message):
        message_id = getattr(message, "id", None)
        if message_id and (source_key, message_id) in self.seen_messages:
            return
        if message_id:
            self.seen_messages.add((source_key, message_id))
        await self.queues[source_key].put(message)

    async def wait(self, source_key):
        try:
            return await asyncio.wait_for(
                self.queues[source_key].get(),
                timeout=self.timeout,
            )
        except asyncio.TimeoutError:
            return None

    def bind_client(self, client, source_resolver=None):
        if not client:
            return

        @client.on_message()
        async def handler(_, message):
            key = source_resolver(message) if source_resolver else None
            if key:
                await self.push(key, message)

def build_source_resolver(sources):
    def resolve(message):
        username = ""
        if getattr(message, "from_user", None):
            username = (message.from_user.username or "").lower()

        for key, source in sources.items():
            bot = source.get("bot", "") if isinstance(source, dict) else getattr(source, "bot", "")
            if str(bot).replace("@", "").lower() == username:
                return key
        return None
    return resolve
