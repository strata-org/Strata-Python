# An attribute target of a parameter that a call of stub b lacks: it applies only to stub a's calls.
from typing import Literal, overload


class Conn:
    state: int


@overload
@modifies(lambda conn: conn.state)
def use(kind: Literal["a"], conn: Conn) -> None:
    ...


@overload
def use(kind: Literal["b"]) -> None:
    ...
