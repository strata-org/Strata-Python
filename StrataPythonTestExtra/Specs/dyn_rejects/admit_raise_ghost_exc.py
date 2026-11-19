ghost(name="exc", type=int, init=0)

@admit_raise(lambda exc: isinstance(exc, Exception))
def f() -> None:
    ...
