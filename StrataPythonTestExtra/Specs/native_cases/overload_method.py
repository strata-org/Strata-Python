from typing import Any, overload

# The @overload stubs of a method are recorded, and they get no Laurel procedure.
# A plain definition of the same name, and any other method, get one.
class C:
    @overload
    def m(self, x: int) -> None:
        ...

    @overload
    def m(self, x: str) -> None:
        ...

    def n(self) -> None:
        ...


class D:
    @overload
    def m(self, x: int) -> None:
        ...

    @overload
    def m(self, x: str) -> None:
        ...

    def m(self, x: Any) -> None:
        ...
