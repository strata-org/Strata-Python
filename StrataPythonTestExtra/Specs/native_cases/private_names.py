# CPython renames each private name __x of a class body to _C__x.
from typing import List

__T = int

class C:
    __f: int
    Y = __T
    class __Inner:
        pass
    def __m(self) -> None:
        ...
    def k(self, *, __a: int, **__kw: int) -> None:
        ...
    def n(self, a: __T) -> None:
        ...
    @admit(lambda self, other, result: other.__y > 0)
    def p(self, other: int) -> None:
        ...
    def __init__(self) -> None:
        self.__g = self._H()
    def q(self, o: int, xs: List[int]) -> None:
        assert o.__z > 0
        if o.__c:
            assert o > 0
        for __i in xs:
            assert __i > 0
