# String ordering is not a numeric post-state comparison.
@admit(lambda x, result: result >= OLD(x))
def f(x: str) -> str:
    ...
