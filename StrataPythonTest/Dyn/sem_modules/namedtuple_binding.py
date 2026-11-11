# The binding errors of a named tuple's __new__ and _make, in CPython's order.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
for f in (lambda: P(1, 2, 3, x=5), lambda: P(1, 2, 3, w=1), lambda: P(1, 2, 3), lambda: P(y=1),
          lambda: P(), lambda: P._make(), lambda: P(1)._replace(1), lambda: P(1)._asdict(1),
          lambda: P(1).__repr__(2), lambda: P(1).__getnewargs__(1), lambda: P._make([1], x=2)):
    try:
        f()
    except TypeError as e:
        print("TypeError:", e)
class Z(NamedTuple):
    pass
print(Z(), Z.__doc__, Z._fields)
try:
    Z(1)
except TypeError as e:
    print("TypeError:", e)
class O(NamedTuple):
    a: int
print(O.__doc__, O(1), O.__new__.__doc__ if False else "")
try:
    O(1, 2)
except TypeError as e:
    print("TypeError:", e)
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
for f in (lambda: P._make([1], 2, x=5), lambda: P(1)._replace(2, x=1), lambda: P._make([1], 2, iterable=5),
          lambda: P(1).__repr__(2, a=1), lambda: P(**{"x": 1, "y": 2, "z": 3}), lambda: P(1, **{"y": 2}),
          lambda: P.__new__(), lambda: P.__new__(P), lambda: P.__new__(5, 1), lambda: P.__new__(int, 1),
          lambda: P.__new__(type(P.x), 1)):
    try:
        print(f())
    except TypeError as e:
        print("TypeError:", e)
print(P.__new__(tuple, 1, 2), type(P.__new__(tuple, 1, 2)))
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
for f in (lambda: P.__new__(_cls=P, x=1), lambda: P(_cls=1, x=2), lambda: P(1, 2, 3, 4, x=1, w=2),
          lambda: P(1, w=2, x=3), lambda: P(1, 2, 3, y=4)):
    try:
        print(f())
    except TypeError as e:
        print("TypeError:", e)
