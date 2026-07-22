import asyncio

class CommandCrawler:
    def __init__(self, client, source, watcher, forwarder, jobs=None, max_retry=5):
        self.client = client
        self.source = source
        self.watcher = watcher
        self.forwarder = forwarder
        self.jobs = jobs
        self.max_retry = max_retry

    async def run(self, start_id):
        current_id = int(start_id)

        lock = self.jobs.lock(self.source.key) if self.jobs else None
        if lock:
            await lock.acquire()

        try:
            while True:
                success = False

                for attempt in range(self.max_retry):
                    await self.client.send_message(
                        self.source.bot,
                        f"{self.source.command} {current_id}",
                    )

                    response = await self.watcher.wait(self.source.key)

                    if response:
                        await self.forwarder.forward(self.client, response)
                        current_id += 1
                        if self.jobs:
                            await self.jobs.update(
                                self.source.key,
                                current_id=current_id,
                                retry=0,
                                last_message_id=getattr(response, "id", None),
                            )
                        success = True
                        break

                    if self.jobs:
                        await self.jobs.update(
                            self.source.key,
                            retry=attempt + 1,
                        )

                if not success:
                    if self.jobs:
                        await self.jobs.update(
                            self.source.key,
                            status="paused",
                        )
                    break

                await asyncio.sleep(1)
        finally:
            if lock and lock.locked():
                lock.release()
