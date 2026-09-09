# EXAMPLE 4 -- a fact about the SOURCE learned AFTER the comprehension.
# Only provenance transfers it.  C model: ex4_late.c
from typing import TypedDict, List

class Item(TypedDict):
    code: int

class ItemsResponse(TypedDict):
    items: List[Item]

def get_items() -> ItemsResponse:
    return {"items": [{"code": 500}, {"code": 501}, {"code": 900}]}

def main() -> None:
    resp = get_items()
    codes = [it['code'] + 1 for it in resp['items'] if it['code'] > 500]

    # learned only now -- a later guard narrows the SOURCE list
    for it in resp['items']:
        if it['code'] == 777:
            return

    # therefore no result element can be 778
    for c in codes:
        assert c != 778

main()
