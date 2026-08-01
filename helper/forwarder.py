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

            if target is None:
                log.warning("Skipping forward: invalid target %s", self.target_chat)
                return False

            await message.forward(target)
            return True

        except Exception as exc:
            log.warning("forward failed for %s: %s", self.target_chat, exc)
            return False
