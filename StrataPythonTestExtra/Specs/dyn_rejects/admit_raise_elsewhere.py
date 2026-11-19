@admit(lambda result: exc >= 0)
def f() -> int:
    ...

@requires(lambda exc: exc >= 0)
def g(n: int) -> None:
    ...

@modifies(lambda exc: exc)
def h(n: int) -> None:
    ...
