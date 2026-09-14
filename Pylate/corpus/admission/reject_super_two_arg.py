"""`super-form`: only the zero-argument `super()` is admitted.

The zero-argument form fixes the owner class lexically, which is what makes the
MRO suffix well defined at the call. `super(C, self)` names the owner as a
runtime expression, so it is refused rather than resolved.
"""


class Base:
    def __init__(self) -> None:
        self.n: int = 0


class Sub(Base):
    def __init__(self) -> None:
        super(Sub, self).__init__()
