# OLD in @requires must be a hard error because it is a pre-state predicate.
@requires(lambda x: OLD(x) >= 0)
def f(x: int) -> int:
    ...
