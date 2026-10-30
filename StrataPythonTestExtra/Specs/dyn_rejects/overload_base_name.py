# A base that names its first parameter differently from its stubs: put(mode="a") binds at run time,
# but the extern would require the stubs' name 'kind'.
from typing import Literal, overload


@overload
def put(kind: Literal["a"]) -> None:
    ...


@overload
def put(kind: Literal["b"]) -> None:
    ...


def put(mode: str) -> None:
    ...
