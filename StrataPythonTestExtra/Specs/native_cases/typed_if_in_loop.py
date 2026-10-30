# An if over a TypedDict element's field, in a loop, records nothing.
from typing import List, TypedDict

Entry = TypedDict('Entry', {'Kind': str, 'Size': int})

def f(entries: List[Entry]) -> None:
    for e in entries:
        if e["Kind"] == "big":
            assert e["Size"] >= 10, "a big entry is at least 10"
