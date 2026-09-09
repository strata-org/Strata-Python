# Negative pair: the mapped result contains 779 when the source contains 778.
from typing import List, TypedDict


class Item(TypedDict):
    code: int


class ItemsResponse(TypedDict):
    items: List[Item]


def get_items() -> ItemsResponse:
    return {"items": [{"code": 500}, {"code": 778}, {"code": 900}]}


def main() -> None:
    items = get_items()["items"]
    codes = [item["code"] + 1 for item in items if item["code"] > 500]
    for code in codes:
        assert code != 779


main()
