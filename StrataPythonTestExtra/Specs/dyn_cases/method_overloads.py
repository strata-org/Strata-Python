from typing import overload, Literal

class C:
    @overload
    def m(self, kind: Literal["a"]) -> int:
        ...

    @overload
    def m(self, kind: Literal["b"]) -> str:
        ...
