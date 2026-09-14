"""`shape-store`: `__class__` assignment retags a live object.

Tag immutability is what makes a dispatch site's switch arms exhaustive. Measured
before the rule existed: this program reported `r = 1`, where CPython answers 2,
because the store was filed as an obligation and the retag ignored.
"""


class A:
    def m(self) -> int:
        return 1


class B:
    def m(self) -> int:
        return 2


def retag() -> int:
    a: A = A()
    a.__class__ = B
    return a.m()
