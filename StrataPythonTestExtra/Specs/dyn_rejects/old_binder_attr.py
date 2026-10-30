from typing import List

class Inner:
    n: int

@admit(lambda xs, result: all(OLD(x.n) + 1 == x.n for x in xs))
def f(xs: List[Inner]) -> None:
    ...
