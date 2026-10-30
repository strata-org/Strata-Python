# Optional takes exactly one argument, as in CPython.
from typing import Optional


def f(a: Optional[str, int]) -> None:
    ...
