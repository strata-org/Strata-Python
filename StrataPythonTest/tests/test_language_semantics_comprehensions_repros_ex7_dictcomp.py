# EXAMPLE 7 -- DICT comprehension.  C model: ex7_dictcomp.c
# Python clash rule is ASYMMETRIC (verified on CPython 3):
#   KEY object + insertion POSITION -> FIRST occurrence
#   VALUE                           -> LAST  occurrence
from typing import TypedDict, List, Dict

class Item(TypedDict):
    ident: int

class ItemsResponse(TypedDict):
    items: List[Item]

def get_items() -> ItemsResponse:
    return {
        "items": [
            {"ident": 100},
            {"ident": 501},
            {"ident": 501},
            {"ident": 502},
        ]
    }

def main() -> None:
    resp = get_items()
    # The C encoding uses a NON-INJECTIVE key (`// 2`) so that clashes are real and
    # the two-witness contract is actually exercised; with an injective key the
    # tiering in doc 5.3a collapses this to the filtered LIST case.
    by_id = {it['ident']: it['ident'] * 2 for it in resp['items'] if it['ident'] > 500}
    assert len(by_id) <= len(resp['items'])

main()
