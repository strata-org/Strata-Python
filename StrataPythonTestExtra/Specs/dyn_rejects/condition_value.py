from re import compile
from typing import List

@admit(lambda x, result: (x or 3) == result)
def g(x: int) -> int: ...

@admit(lambda x, result: result == (x and 7))
def h(x: int) -> int: ...

def k(x: int, y: int) -> int:
    assert (x or y) >= 1

def m(s: str) -> None:
    assert compile("a").search(s) == False

@admit(lambda x, result: (x != "A") == result)
def n(x: str) -> bool: ...

@admit(lambda x, result: (not (x != "A")) == result)
def q(x: str) -> bool: ...

def r(xs: List[str], flag: bool) -> None:
    assert all(x == "A" or x == "B" for x in xs) == flag
