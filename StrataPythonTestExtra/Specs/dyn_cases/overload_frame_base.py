# An overload set with a base: the base's own frame applies to every call, and each stub's targets only to its own.
from typing import List, Literal, overload


@overload
@modifies(lambda xs: xs)
def put(kind: Literal["a"], xs: List[int]) -> None:
    ...


@overload
def put(kind: Literal["b"]) -> None:
    ...


@modifies(lambda ys: ys)
def put(kind: str, ys: List[int]) -> None:
    ...
