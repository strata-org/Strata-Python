"""`super-builtin-base`: a subclass can splice a builtin into the chain.

`Mid.m` delegates, and on `Mid`'s own MRO the chain is all user code. But `Sub`
puts `ValueError` between `Mid` and `object`, so a `Sub` receiver would send
`Mid`'s `super()` into a builtin. The check therefore runs over every class that
could *be* the receiver, not only the class the call is written in.
"""


class Base:
    def __init__(self) -> None:
        self.n: int = 0

    def m(self) -> int:
        return 1


class Mid(Base):
    def m(self) -> int:
        return 10 + super().m()


class Sub(Mid, ValueError):
    pass
