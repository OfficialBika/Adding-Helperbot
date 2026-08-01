import hashlib


class ImageSimilarityService:
    """Lightweight image similarity foundation.

    Designed to be extended with pHash/dHash algorithms.
    """

    def generate_fingerprint(self, content: bytes) -> str:
        return hashlib.md5(content).hexdigest()

    def similarity_score(self, first: str, second: str) -> float:
        if first == second:
            return 1.0
        return 0.0


image_similarity_service = ImageSimilarityService()
