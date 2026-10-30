from typing import overload

# An @overload stub's body is not read, so an assert in it is rejected.
class P:
    @overload
    def m(self, x: int) -> int:
        assert x <= 5, "x is small"

    @overload
    def m(self, x: str) -> int:
        ...
