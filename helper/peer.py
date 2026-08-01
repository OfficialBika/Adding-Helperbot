import logging

logger = logging.getLogger(__name__)


async def resolve_peer(client, peer):
    """Safely resolve Telegram peers without crashing workers."""
    if peer is None:
        return None

    if isinstance(peer, int):
        return peer

    value = str(peer).strip()
    if not value:
        return None

    if value.lstrip("-").isdigit():
        return int(value)

    try:
        user = await client.get_users(value.lstrip("@"))
        return user.id
    except Exception as exc:
        logger.warning("Failed resolving peer %s: %s", value, exc)
        return None


async def safe_send_message(client, peer, text, **kwargs):
    """Send message only after peer validation."""
    target = await resolve_peer(client, peer)
    if target is None:
        logger.warning("Skipped message: invalid peer %s", peer)
        return None

    try:
        return await client.send_message(target, text, **kwargs)
    except Exception as exc:
        logger.warning("Send failed for peer %s: %s", target, exc)
        return None
