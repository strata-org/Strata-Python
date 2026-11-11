# cast, TYPE_CHECKING, overload, Any, TypeGuard, NotRequired, Required, ForwardRef.
import typing
from typing import cast, TYPE_CHECKING, overload, Any, TypeGuard, NotRequired, Required, Optional
print(cast(int, "a"), TYPE_CHECKING, typing.TYPE_CHECKING)
@overload
def f(x: int) -> int: ...
print(f.__name__)
try:
    f(1)
except NotImplementedError as e:
    print("NotImplementedError:", e)
print(Any, TypeGuard[int], NotRequired[int], Required[str])
try:
    Any()
except TypeError as e:
    print("TypeError:", e)
try:
    isinstance(1, Any)
except TypeError as e:
    print("TypeError:", e)
r = Optional["Node"]
print(r, r.__args__[0] == Optional["Node"].__args__[0])
def g(x: Optional[int] = None) -> list[int]:
    return [x]
print(g.__annotations__)
