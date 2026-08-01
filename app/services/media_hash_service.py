import hashlib


class MediaHashService:
    """Generate fingerprints for fast media duplicate detection."""

    def sha256(self, content: bytes) -> str:
        return hashlib.sha256(content).hexdigest()

    def compare_hashes(self, first: str, second: str) -> bool:
        return first == second


media_hash_service = MediaHashService()
