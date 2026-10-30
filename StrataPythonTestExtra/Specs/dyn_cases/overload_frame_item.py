# An item target of a parameter that a call of stub b lacks: it applies only to stub a's calls.
from typing import Dict, Literal, overload


@overload
@modifies(lambda d: d["k"])
def put(kind: Literal["a"], d: Dict[str, int]) -> None:
    ...


@overload
def put(kind: Literal["b"]) -> None:
    ...
