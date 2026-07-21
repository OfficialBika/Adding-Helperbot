import asyncio

class CommandCrawler:
    def __init__(self, client, source, watcher, forwarder, max_retry=5):
        self.client=client
        self.source=source
        self.watcher=watcher
        self.forwarder=forwarder
        self.max_retry=max_retry

    async def run(self, start_id):
        current_id=int(start_id)
        while True:
            for attempt in range(self.max_retry):
                await self.client.send_message(
                    self.source.bot,
                    f"{self.source.command} {current_id}"
                )
                # Response watcher integration point.
                response = await self.watcher.wait(self.client)
                if response:
                    await self.forwarder.forward(self.client, response)
                    current_id += 1
                    break
            else:
                return
            await asyncio.sleep(1)
