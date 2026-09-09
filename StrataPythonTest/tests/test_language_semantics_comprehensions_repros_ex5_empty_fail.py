# Negative pair: a zero divisor in the source must be reported.
from typing import List, TypedDict


class Item(TypedDict):
    divisor: int


class ItemsResponse(TypedDict):
    items: List[Item]


def get_items() -> ItemsResponse:
    return {"items": [{"divisor": 4}, {"divisor": 0}]}


def main() -> None:
    items = get_items()["items"]
    ratios = [100 // item["divisor"] for item in items]
    assert len(ratios) == len(items)


main()
