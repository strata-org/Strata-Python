# Native @admit_raise: what holds when a call raises, with the `exc` binder.
@admit_raise(lambda exc: isinstance(exc, Exception))
@admit_raise(lambda exc, n: n >= 0)
def f(n: int) -> int:
    ...

@admit_raise(lambda exc: False)
def g() -> None:
    ...

@admit_raise(lambda e: isinstance(e, Exception))
def h() -> None:
    ...
