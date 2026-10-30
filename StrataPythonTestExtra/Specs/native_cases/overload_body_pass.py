from typing import overload

# A stub whose body is not `...` gets a warning.
@overload
def f(x: int) -> int:
    pass

@overload
def f(x: str) -> int:
    ...
