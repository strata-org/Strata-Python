# EXAMPLE 3 -- a property that relates TWO result positions.
# Needs the strict-monotonicity axiom.  C model: ex3_order.c
from typing import TypedDict, List

class Reading(TypedDict):
    ts: int

class ReadingsResponse(TypedDict):
    readings: List[Reading]

def get_readings() -> ReadingsResponse:
    return {
        "readings": [
            {"ts": 900},
            {"ts": 1001},
            {"ts": 1001},
            {"ts": 2000},
        ]
    }

def main() -> None:
    resp = get_readings()
    recent = [r['ts'] for r in resp['readings'] if r['ts'] > 1000]
    # A filter PRESERVES sortedness -- but only provable if the encoding
    # records that antecedents keep their relative order.
    for i in range(1, len(recent)):
        assert recent[i - 1] <= recent[i]

main()
