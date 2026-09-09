# U2 srclen
from typing import TypedDict, List

class Item(TypedDict):
    ident: int

class Resp(TypedDict):
    items: List[Item]

def get_items() -> Resp:
    return {"items": [{"ident": 1}, {"ident": 2}]}

def main() -> None:
    resp = get_items()
    n = len(resp['items'])
    assert n >= 0          # should be trivially TRUE
main()
