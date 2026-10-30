# A def that rebinds a name from typing rejects the model.
from typing import List


def List() -> int:
    ...


def f(xs: List[int]) -> None:
    ...
