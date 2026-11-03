# A | of types, or of a type and None, evaluates under CPython.
from typing import List

X = int | None
Y = None | List[int]

def f(x: X, y: Y) -> None:
    ...
