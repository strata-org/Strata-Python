# OLD is valid in an admitted post-state predicate.
@admit(lambda x, result: result >= OLD(x))
def f(x: int) -> int:
    ...
