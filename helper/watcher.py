import asyncio
from collections import defaultdict
from pyrogram import filters

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
            return await asyncio.wait_for(self.queues[source_key].get(), timeout=self.timeout)
        except asyncio.TimeoutError:
            return None

    def bind_client(self, client, source_resolver=None):
        if not client:
            return

        @client.on_message(filters.private)
        async def handler(_, message):
            try:
                key = source_resolver(message) if source_resolver else None
                if key:
                    await self.push(key, message)
            except Exception:
                return

def build_source_resolver(sources):
    normalized = {}
    for key, source in sources.items():
        bot = source.get("bot", "") if isinstance(source, dict) else getattr(source, "bot", "")
        normalized[str(bot).replace("@","").lower()] = key

    def resolve(message):
        candidates = []
        if getattr(message, "from_user", None):
            candidates.append(getattr(message.from_user, "username", "") or "")
        if getattr(message, "chat", None):
            candidates.append(getattr(message.chat, "username", "") or "")

        for item in candidates:
            key = normalized.get(str(item).replace("@","").lower())
            if key:
                return key
        return None

    return resolve
