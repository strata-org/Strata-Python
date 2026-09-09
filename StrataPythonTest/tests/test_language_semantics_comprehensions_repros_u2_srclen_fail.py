# Negative pair: a concrete source list cannot have negative length.
from typing import List, TypedDict


class Item(TypedDict):
    ident: int


class Resp(TypedDict):
    items: List[Item]


def get_items() -> Resp:
    return {"items": [{"ident": 1}, {"ident": 2}]}


def main() -> None:
    item_count = len(get_items()["items"])
    assert item_count < 0


main()
