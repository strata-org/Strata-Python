# `len` of a `str` is a string length; `len` of anything else is the generic `len`.
from typing import Any, List

def f(xs: List[str], s: str, a: Any) -> None:
    assert len(xs) >= 1, "xs must not be empty"
    assert len(s) >= 1, "s must not be empty"
    assert len(a) <= 3, "a has at most three elements"
