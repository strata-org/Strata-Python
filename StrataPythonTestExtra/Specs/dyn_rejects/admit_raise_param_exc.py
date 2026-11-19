from typing import NotRequired, TypedDict, Unpack

@admit_raise(lambda exc: exc >= 0)
def f(exc: int) -> None:
    ...

@admit_raise(lambda exc: isinstance(exc, Exception))
def g(*, exc: int) -> None:
    ...

KW = TypedDict('KW', {'a': NotRequired[int]})

@admit_raise(lambda exc: isinstance(exc, Exception))
def h(**exc: Unpack[KW]) -> None:
    ...
