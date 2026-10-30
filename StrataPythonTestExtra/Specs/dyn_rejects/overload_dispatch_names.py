# Stubs that name their first parameter differently: stub b's 'kind' would lose its clauses.
from typing import Literal, overload


@overload
def f(kind: Literal["a"]) -> int:
    ...


@overload
@admit(lambda result: result >= 0)
def f(mode: Literal["b"], kind: int) -> int:
    ...
