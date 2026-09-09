# Negative pair: a dict comprehension cannot have more keys than source items.
from typing import Dict, List, TypedDict


class Item(TypedDict):
    ident: int


class ItemsResponse(TypedDict):
    items: List[Item]


def get_items() -> ItemsResponse:
    return {"items": [{"ident": 501}, {"ident": 501}, {"ident": 502}]}


def main() -> None:
    items = get_items()["items"]
    by_id: Dict[int, int] = {
        item["ident"]: item["ident"] * 2
        for item in items
        if item["ident"] > 500
    }
    assert len(by_id) > len(items)


main()
