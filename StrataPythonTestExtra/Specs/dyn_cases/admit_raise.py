# Postconditions of a raising call (docs/PythonToDyn.md §12.3, @admit_raise): each holds on the
# raising exit, with `exc` bound to the raised exception, and is true on a return.
from typing import Literal, overload

ghost(name="calls", type=int, init=0)

@admit_raise(lambda exc: isinstance(exc, Exception))
def call(region: str) -> int:
    ...

@admit_raise(lambda exc: False)
def report(total: int) -> None:
    ...

@admit_raise(lambda exc, n: OLD(n) >= 0)
@admit_raise(lambda exc: calls >= 0)
@admit(lambda n, result: OLD(n) >= 0)
def count(n: int) -> None:
    ...

@admit_raise(lambda e: e >= 0)
def misnamed(e: int) -> None:
    ...

class Client:
    @admit_raise(lambda exc: isinstance(exc, Exception))
    def get(self, key: str) -> str:
        ...

@overload
@admit_raise(lambda exc: False)
def fetch(kind: Literal["a"]) -> int:
    ...

@overload
@admit_raise(lambda exc: isinstance(exc, Exception))
def fetch(kind: Literal["b"]) -> str:
    ...

@admit_raise(lambda exc: isinstance(exc, Exception))
def fetch(kind: str) -> None:
    ...
