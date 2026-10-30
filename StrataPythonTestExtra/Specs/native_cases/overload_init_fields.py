from typing import overload

# Two @overload stubs of __init__ that assign the same field declare it once.
class C:
    class _H:
        pass

    @overload
    def __init__(self, x: int) -> None:
        self.h = self._H()

    @overload
    def __init__(self, x: str) -> None:
        self.h = self._H()
