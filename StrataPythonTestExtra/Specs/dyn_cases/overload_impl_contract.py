# A method's @overload stubs and its implementation share one list in PySpec. Only the
# implementation gives the method's extern its contract: its precondition and its return type
# Any, not the stubs' int and str.
from typing import Any, overload

class C:
    @overload
    def m(self, x: int) -> int:
        ...

    @overload
    def m(self, x: str) -> str:
        ...

    @requires(lambda self, x: x is not None)
    def m(self, x: Any) -> Any:
        ...
