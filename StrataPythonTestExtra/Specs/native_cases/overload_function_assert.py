from typing import overload

# An @overload stub's body is not read, so an assert in it is rejected.
@overload
def f(x: int) -> int:
    assert x > 0
    ...

@overload
def f(x: str) -> int:
    ...
