from typing import List


class Inner:
    x: int


class C:
    @admit(lambda self, xs, result: all(self.x >= 0 for self in xs))
    def m(self, xs: List[Inner]) -> int:
        ...
