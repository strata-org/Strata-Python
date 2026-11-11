# NamedTuple in class syntax.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
    def norm(self):
        return self.x + self.y
p = P(1)
print(p, p.x, p[0], p.norm(), len(p), p == (1, 0))
print(P._fields, P._field_defaults, P.__doc__, P.__match_args__, P.__dict__["__annotations__"])
print(p._replace(x=5), p._asdict(), P._make([3, 4]))
print(isinstance(p, tuple), P.__mro__)
try:
    p.foo = 1
except AttributeError as e:
    print("AttributeError:", e)
try:
    P._make([1, 2, 3])
except TypeError as e:
    print("TypeError:", e)
try:
    P()
except TypeError as e:
    print("TypeError:", e)
try:
    class Q(NamedTuple):
        x: int = 0
        y: int
except TypeError as e:
    print("TypeError:", e)
try:
    class R(NamedTuple):
        x: int
        def _make(cls):
            pass
except AttributeError as e:
    print("AttributeError:", e)
class L(NamedTuple):
    a: int
    b: int
    def __len__(self):
        return 2
q = L._make([1, 2, 3])
print(q[0], q[1], q[2], q.a, len(q))
try:
    repr(q)
except TypeError as e:
    print("TypeError:", e)
# _make over a user iterator calls tuple.__new__, the library's.
class It:
    def __init__(self):
        self.n = 0
    def __iter__(self):
        return self
    def __next__(self):
        self.n += 1
        if self.n > 2:
            raise StopIteration
        return self.n
print(P._make(It()))
