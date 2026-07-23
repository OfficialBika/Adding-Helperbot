
import logging
log = logging.getLogger(__name__)

async def resolve_peer(client, peer):
    """Safely resolve telegram peers before sending."""
    if peer is None:
        raise ValueError("empty peer")

    if isinstance(peer, int):
        return peer

    value = str(peer).strip()
    if value.lstrip("-").isdigit():
        return int(value)

    user = await client.get_users(value.lstrip("@"))
    return user.id
