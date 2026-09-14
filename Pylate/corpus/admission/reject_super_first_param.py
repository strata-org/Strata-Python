"""`super-form`: `super()` needs the first parameter to be named `self`.

The zero-argument form binds CPython's *first positional argument*, whatever it
is called, while the analysis reads the receiver out of the binding named `self`.
Measured before this rule existed: with the first parameter named `this`, the
`super()` dispatch found no receiver, no arm ran, and the call returned bottom --
`Sub().m()` produced no value and filed no obligation, where CPython answers 11.
A silent bottom makes admitted code unreachable and discharges later obligations
for free, so the mismatch is refused rather than analysed.
"""


class Base:
    def __init__(self) -> None:
        self.n: int = 0

    def m(self) -> int:
        return 1


class Sub(Base):
    def m(this) -> int:
        return 10 + super().m()
