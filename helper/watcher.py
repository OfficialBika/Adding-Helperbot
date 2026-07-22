import asyncio

class ResponseWatcher:
    def __init__(self, timeout=30):
        self.timeout = timeout

    async def wait(self, client, check=None):
        # Event binding hook for Pyrogram handler.
        # Returns None until a response collector is connected.
        await asyncio.sleep(0)
        return None
