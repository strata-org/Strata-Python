# @requires accepts no keyword arguments; an unexpected one is a hard error.
@requires(lambda x: x >= 0, foo=1)
def f(x: int) -> int:
    ...
