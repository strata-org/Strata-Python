from typing import Literal, overload

@exhaustive
class C:
    n: int

    @overload
    def m(self, kind: Literal["a"]) -> int:
        ...

    @overload
    def m(self, kind: Literal["b"]) -> str:
        ...
