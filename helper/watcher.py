import asyncio
from collections import defaultdict
from pyrogram import filters

class ResponseWatcher:
    def __init__(self, timeout=45):
        self.timeout = timeout
        self.queues = defaultdict(asyncio.Queue)
        self.seen_messages = set()

    async def push(self, source_key, message):
        mid = getattr(message, "id", None)
        if mid and (source_key, mid) in self.seen_messages:
            return
        if mid:
            self.seen_messages.add((source_key, mid))
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

        @client.on_message(filters.private)
        async def handler(_, message):
            key = None
            try:
                if source_resolver:
                    key = source_resolver(message)
                if key:
                    await self.push(key, message)
            except Exception:
                pass


def build_source_resolver(sources):
    lookup = {}
    for key, src in sources.items():
        names = [
            str(src.get("bot","")).lstrip("@").lower()
        ]
        for n in names:
            lookup[n] = key

    def resolve(message):
        values=[]
        if getattr(message,"from_user",None):
            values.append(getattr(message.from_user,"username","") or "")
            values.append(str(getattr(message.from_user,"id","")))
        if getattr(message,"chat",None):
            values.append(getattr(message.chat,"username","") or "")
            values.append(str(getattr(message.chat,"id","")))

        for v in values:
            v=str(v).lstrip("@").lower()
            for name,key in lookup.items():
                if v and v == name:
                    return key
        return None
    return resolve
