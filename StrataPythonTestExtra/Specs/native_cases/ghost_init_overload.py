# CPython runs the decorators of an overload stub when it imports the model.
from typing import Literal, overload

@overload
@ghost(name="g", type=int, init=len("ab"))
def f(x: Literal["a"]) -> int:
    ...

@overload
def f(x: Literal["b"]) -> int:
    ...
