# Negative pair: a set comprehension cannot outgrow its source.
from typing import List, Set, TypedDict


class Item(TypedDict):
    region: int


class ItemsResponse(TypedDict):
    items: List[Item]


def get_items() -> ItemsResponse:
    return {"items": [{"region": 501}, {"region": 501}, {"region": 700}]}


def main() -> None:
    items = get_items()["items"]
    regions: Set[int] = {
        item["region"] + 1 for item in items if item["region"] > 500
    }
    assert len(regions) > len(items)


main()
