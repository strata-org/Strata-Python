# Stub b names its first parameter 'mode', and makes 'kind', stub a's first parameter, keyword-only.
from typing import List, Literal, overload


@overload
def f(kind: Literal["a"]) -> int:
    ...


@overload
def f(mode: Literal["b"], *, kind: List[int]) -> int:
    ...
