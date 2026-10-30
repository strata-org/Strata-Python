from typing import List

@modifies(lambda xs: xs)
@admit(lambda xs, x, result: (x in xs) and not OLD(x in xs))
def add(xs: List[int], x: int) -> None:
    ...
