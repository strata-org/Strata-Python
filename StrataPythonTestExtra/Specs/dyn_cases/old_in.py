from typing import List

@admit(lambda xs, x, result: (x in xs) and not OLD(x in xs))
def f(xs: List[int], x: int) -> None:
    ...
