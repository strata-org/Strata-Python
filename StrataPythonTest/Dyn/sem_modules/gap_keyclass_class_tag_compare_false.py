# Two classes share a plain __class__; B's field(compare=False) holds a user object.
from dataclasses import dataclass, field
M = 2**61 - 1
TAG = object()
n = [0]
class U:
    def __eq__(self, o):
        n[0] += 1
        return True
    __hash__ = object.__hash__
@dataclass(frozen=True)
class A:
    x: int
    y: object = field(default=0, hash=False)
    __class__ = TAG
@dataclass(frozen=True)
class B:
    x: int
    y: object = field(default=None, compare=False)
    __class__ = TAG
d = {A(1, 10): "first", A(1 + M, 20): "second"}
print(d.get(B(1, U())), n[0])
