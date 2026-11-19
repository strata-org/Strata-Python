from typing import Literal, overload

class C:
    @overload
    @admit_raise(lambda exc: False)
    def m(self, k: Literal["a"]) -> int:
        ...

    @overload
    def m(self, k: Literal["b"]) -> str:
        ...
