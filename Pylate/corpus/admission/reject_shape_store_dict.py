"""`shape-store`: writing `__dict__` replaces the instance schema wholesale.

Measured before the rule existed: `a.__dict__ = {}` then `a.n` reported
`int lit=0`, where CPython raises `AttributeError`.
"""


class A:
    def __init__(self) -> None:
        self.n: int = 0


def wipe() -> int:
    a: A = A()
    a.__dict__ = {}
    return a.n
