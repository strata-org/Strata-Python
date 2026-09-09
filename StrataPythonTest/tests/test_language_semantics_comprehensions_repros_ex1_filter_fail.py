# Negative pair: filtering cannot produce more elements than its source.
from typing import List, TypedDict


class Metric(TypedDict):
    value: int


class MetricsResponse(TypedDict):
    metrics: List[Metric]


def get_metrics() -> MetricsResponse:
    return {"metrics": [{"value": 100}, {"value": 501}, {"value": 700}]}


def main() -> None:
    metrics = get_metrics()["metrics"]
    hot = [metric["value"] + 1 for metric in metrics if metric["value"] > 500]
    assert len(hot) > len(metrics)


main()
