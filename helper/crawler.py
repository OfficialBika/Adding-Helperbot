import asyncio

class CommandCrawler:
    def __init__(self, client, source, watcher, forwarder, jobs, max_retry=5):
        self.client=client
        self.source=source
        self.watcher=watcher
        self.forwarder=forwarder
        self.jobs=jobs
        self.max_retry=max_retry

    async def run(self, start_id):
        current_id=int(start_id)

        while True:
            success=False

            for attempt in range(1, self.max_retry+1):
                self.jobs.jobs[self.source.key]["retry"]=attempt

                await self.client.send_message(
                    self.source.bot,
                    f"{self.source.command} {current_id}"
                )

                response = await self.watcher.wait(
                    self.source.key
                )

                if response:
                    await self.forwarder.forward(
                        self.client,
                        response
                    )
                    current_id += 1
                    self.jobs.update_id(
                        self.source.key,
                        current_id
                    )
                    success=True
                    break

                await asyncio.sleep(3)

            if not success:
                self.jobs.stop(self.source.key)
                return

            await asyncio.sleep(1)
