# A ghost of type Any that a call may change keeps the invariant that it is defined.
from typing import Any

ghost(name="limit", type=Any, init=0)


@modifies(lambda: limit)
def reset() -> None:
    ...


@requires(lambda x: x <= limit)
def f(x: int) -> None:
    ...
