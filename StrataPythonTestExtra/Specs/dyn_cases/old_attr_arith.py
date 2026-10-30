class Counter:
    n: int

@admit(lambda c, result: c.n == OLD(c.n) + 1)
def inc(c: Counter) -> None:
    ...
