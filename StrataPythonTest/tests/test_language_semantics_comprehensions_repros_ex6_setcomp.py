# EXAMPLE 6 -- SET comprehension.  C model: ex6_setcomp.c
# Python clash rule (verified on CPython 3): the FIRST occurrence's object is
# retained; later equal elements are dropped entirely.
#
# But slot ORDER is hash-determined, NOT insertion-determined:
#     list({3, 1, 2}) == [1, 2, 3]      not [3, 1, 2]
# so the encoding must NOT carry the list case's monotonicity axiom. Asserting
# anything about which element occupies which slot -- list(s)[0], next(iter(s)) --
# is unprovable and must stay so. See ex6_order_unsound.c for the false proof
# that axiom buys.
from typing import TypedDict, List, Set

class Item(TypedDict):
    region: int

class ItemsResponse(TypedDict):
    items: List[Item]

def get_items() -> ItemsResponse:
    return {
        "items": [
            {"region": 100},
            {"region": 501},
            {"region": 501},
            {"region": 700},
        ]
    }

def main() -> None:
    resp = get_items()
    regions = {it['region'] + 1 for it in resp['items'] if it['region'] > 500}
    # dedup means the result can be SHORTER than the filtered source
    assert len(regions) <= len(resp['items'])

main()
