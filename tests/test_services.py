from app.services.statistics_service import statistics_service


def test_statistics_service():
    statistics_service.add_image()
    data = statistics_service.get()

    assert data["images"] >= 1
