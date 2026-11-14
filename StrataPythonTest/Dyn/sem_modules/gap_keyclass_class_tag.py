# Two classes share a plain __class__, so one's __eq__ accepts the other's instance.
from dataclasses import dataclass, field
M = 2**61 - 1
TAG = object()
@dataclass(frozen=True)
class A:
    x: int
    y: int = field(default=0, hash=False)
    __class__ = TAG
@dataclass(frozen=True)
class B:
    x: int
    __class__ = TAG
    @property
    def y(self):
        return 10
d = {A(1, 10): "first", A(1 + M, 20): "second"}
print(d[B(1)])
