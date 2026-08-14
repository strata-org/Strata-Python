# OLD with wrong arity must be a hard error.
@admit(lambda x, result: OLD(x, x) >= 0)
def f(x: int) -> int:
    ...
