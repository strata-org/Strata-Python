# EXAMPLE 1 -- filtered comprehension.  C model: ex1_filter.c
from typing import TypedDict, List

class Metric(TypedDict):
    value: int

class MetricsResponse(TypedDict):
    metrics: List[Metric]

def get_metrics() -> MetricsResponse:
    return {
        "metrics": [
            {"value": 100},
            {"value": 500},
            {"value": 501},
            {"value": 700},
        ]
    }

def main() -> None:
    resp = get_metrics()
    hot = [m['value'] + 1 for m in resp['metrics'] if m['value'] > 500]
    # every surviving element is > 501, and there are at most as many as inputs
    assert len(hot) <= len(resp['metrics'])

main()
