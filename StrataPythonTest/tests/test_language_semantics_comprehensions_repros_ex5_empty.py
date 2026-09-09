# EXAMPLE 5 -- the empty-list case must stay reachable.
# C model: ex5_empty.c
from typing import TypedDict, List

class Item(TypedDict):
    divisor: int

class ItemsResponse(TypedDict):
    items: List[Item]

def get_items() -> ItemsResponse:
    return {"items": [{"divisor": 4}, {"divisor": 5}]}

def main() -> None:
    resp = get_items()
    # The body divides, so it carries a division-by-zero obligation. That
    # obligation belongs on the representative element -- but if the list is
    # EMPTY the body never runs, and len(ratios) == 0 must remain reachable.
    ratios = [100 // it['divisor'] for it in resp['items']]
    assert len(ratios) == len(resp['items'])

main()
