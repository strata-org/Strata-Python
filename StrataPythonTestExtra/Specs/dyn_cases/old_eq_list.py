from typing import List

@admit(lambda xs, ys, result: OLD(xs == ys))
def f(xs: List[int], ys: List[int]) -> None:
    ...
