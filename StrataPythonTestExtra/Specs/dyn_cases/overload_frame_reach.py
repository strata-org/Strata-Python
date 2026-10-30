# A target that gives py.reachLoc of conn.state, for a parameter that a call of stub b lacks: it
# applies only to stub a's calls.
from typing import Any, Literal, overload


@overload
@modifies(lambda conn: conn.state)
def use(kind: Literal["a"], conn: Any) -> None:
    ...


@overload
def use(kind: Literal["b"]) -> None:
    ...
