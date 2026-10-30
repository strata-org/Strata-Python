# Stub a's frame target reads xs, which a call of stub b lacks: it applies only to stub a's calls.
from typing import List, Literal, overload


@overload
@modifies(lambda xs: xs)
def put(kind: Literal["a"], xs: List[int]) -> None:
    ...


@overload
def put(kind: Literal["b"]) -> None:
    ...
