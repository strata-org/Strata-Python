# The lambdas after a decorator's first are recorded as dropped clauses of its kind.
@requires(lambda x: x > 0, lambda x: x < 10)
@modifies(lambda x: x, lambda x: x)
def f(x: int) -> None:
    ...
