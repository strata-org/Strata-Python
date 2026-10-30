# A module binding of a builtin's name, even one that gives no signature, makes CPython call
# the module's value, so each assert is recorded as dropped.
from re import compile
from typing import List

def uses_all(xs: List[int]) -> None:
    assert all(x > 0 for x in xs)

def uses_len(s: str) -> None:
    assert len(s) >= 1

def uses_compile(s: str) -> None:
    assert compile("a").search(s) is not None

all = None
len = 5
compile = None
