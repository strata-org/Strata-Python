@admit(lambda x, result: result == OLD(x) + 1)
def f(x: int) -> int:
    ...

@admit(lambda x, result: OLD(x > 0) and result > 0)
def g(x: int) -> int:
    ...
