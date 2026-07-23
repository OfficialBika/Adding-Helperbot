
import logging
from .peer import resolve_peer

log = logging.getLogger(__name__)

class HelperForwarder:
    def __init__(self, target_chat):
        self.target_chat = target_chat

    async def forward(self, client, message):
        if not message or not self.target_chat:
            return False
        try:
            target = await resolve_peer(client, self.target_chat)
            await message.forward(target)
            return True
        except Exception:
            log.exception("forward failed")
            return False
