# An annotation that names the class whose body it is in raises NameError when CPython imports
# the module, but PySpec reads it as a stub does.
from typing import Literal

class D:
    def clone(self) -> "D":
        ...

    def same(self) -> D:
        ...

    # The annotation of a method named `int` is read before the method binds `int`.
    def int(self) -> int:
        ...

    # The value of a Literal is a string, not a forward reference.
    def pick(self, name: Literal["same"]) -> str:
        ...

# A quoted name of a class whose name had a binding before stays a string in CPython.
class TimeoutError(Exception):
    def f(self) -> "TimeoutError":
        ...

# PySpec reads the bare name of a nested class at module level, as CPython does.
class I:
    ...

class O:
    class I:
        def f(self) -> I:
            ...

    class int:
        def f(self) -> int:
            ...
