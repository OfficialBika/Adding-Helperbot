
from pyrogram import filters

async def bind_response_handlers(client, controller):
    @client.on_message(filters.private)
    async def _response_handler(_, message):
        # Match incoming private bot responses against active jobs.
        for key, job in controller.jobs.jobs.items():
            source = controller.get_source(key) if hasattr(controller, "get_source") else None
            if source and message.chat and message.chat.username:
                if message.chat.username.lower() == source.bot.lstrip("@").lower():
                    await controller.watcher.push(key, message)
                    break
