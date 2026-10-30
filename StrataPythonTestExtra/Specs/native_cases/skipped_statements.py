# After a statement that PySpec skips and that can change what a later assert means, every
# later assert is recorded as dropped: an assignment, a call, or a walrus.
from typing import List

def assign(s: str, n: int) -> None:
    s = s.strip()
    assert len(s) >= 1, "s is not empty"
    assert n >= 1, "n is positive"

def call(xs: List[int]) -> None:
    xs.pop()
    assert len(xs) > 5, "xs is long"

def annotated_walrus(n: int) -> None:
    y: int = (n := 0)
    assert n >= 1, "n is positive"

def condition_walrus(n: int) -> None:
    if (n := 0) == 0:
        pass
    assert n >= 1, "n is positive"

def rebound_builtin(s: str) -> None:
    str = int
    assert isinstance(s, str), "s is a str"

def untouched(n: int) -> None:
    """A docstring changes nothing."""
    assert n >= 1, "n is positive"

def untranslated_if(xs: List[int]) -> None:
    if xs.pop() > 3:
        raise ValueError("big")
    assert len(xs) > 5, "xs is long"
