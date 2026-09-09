# Negative pair: filtering preserves this deliberately unsorted source order.
from typing import List, TypedDict


class Reading(TypedDict):
    ts: int


class ReadingsResponse(TypedDict):
    readings: List[Reading]


def get_readings() -> ReadingsResponse:
    return {"readings": [{"ts": 1001}, {"ts": 2000}, {"ts": 1500}]}


def main() -> None:
    recent = [
        reading["ts"]
        for reading in get_readings()["readings"]
        if reading["ts"] > 1000
    ]
    for index in range(1, len(recent)):
        assert recent[index - 1] <= recent[index]


main()
