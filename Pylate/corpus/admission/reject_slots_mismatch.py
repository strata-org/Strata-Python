"""`slots-mismatch`: a field assigned but not slotted anywhere on the MRO.

CPython raises `AttributeError` as soon as `__init__` runs, so the class can never
be constructed. Measured: `AttributeError: 'Bad' object has no attribute 'm' and
no __dict__ for setting new attributes`, and mypy agrees --
`Trying to assign name "m" that is not in "__slots__"`. (ty misses this one.)

Rejected rather than analysed, because a class whose constructor cannot complete
is not a shape the encoding can derive anything from.
"""


class Bad:
    __slots__ = ("n",)

    def __init__(self) -> None:
        self.n: int = 0
        self.m: int = 1
