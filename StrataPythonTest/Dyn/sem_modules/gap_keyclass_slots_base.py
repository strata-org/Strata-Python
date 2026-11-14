# A frozen dataclass whose base has __slots__: its instances don't have object's layout.
from dataclasses import dataclass, field
M = 2**61 - 1
class B:
    __slots__ = ("z",)
@dataclass(frozen=True)
class C(B):
    a: int
    b: object = field(default=None, hash=False)
d = {C(1, 10): "first", C(1 + M, 20): "second"}
print(d.get(C(1, 99)), d.get(C(1, 10)))
