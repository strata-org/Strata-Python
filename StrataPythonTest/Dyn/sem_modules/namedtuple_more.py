# More of NamedTuple: the accessors, the generated methods' names and errors, and the class.
from typing import NamedTuple, List, Optional
class P(NamedTuple):
    """A point."""
    x: int
    y: "Node" = []
    z: Optional[int] = None
p = P(1)
print(p, P.x, type(P.x).__name__, type(P.x).__module__, P.x.__doc__, P.y.__get__(p), P.x.__get__(None, P))
print(P.__doc__, P.__qualname__, P.__module__, P.__new__.__qualname__, P.__new__.__module__)
print(P._make.__qualname__, P._replace.__name__, P.__repr__.__qualname__, P._asdict.__module__)
print(P._make((5, 6, 7)), P(z=3, x=2), p.__getnewargs__(), p._replace(z=9), P.__match_args__)
print(type(P.__dict__["__new__"]).__name__, type(P.__dict__["_make"]).__name__, P.__dict__["__slots__"])
print(P.__dict__["__annotations__"], P.__orig_bases__[0].__name__, P._field_defaults)
for bad in (lambda: P(1, 2, 3, 4), lambda: P(1, x=2), lambda: P(1, w=2), lambda: P._make([1]),
            lambda: p._replace(w=1), lambda: P.x.__get__(5)):
    try:
        bad()
    except (TypeError, ValueError) as e:
        print(type(e).__name__ + ":", e)
for bad in (lambda: P.x.__set__(p, 1), lambda: P.x.__delete__(p)):
    try:
        bad()
    except AttributeError as e:
        print("AttributeError:", e)
try:
    p.x = 5
except AttributeError as e:
    print("AttributeError:", e)
try:
    class Q(NamedTuple):
        _a: int
except ValueError as e:
    print("ValueError:", e)
try:
    class R(NamedTuple, P):
        a: int
except TypeError as e:
    print("TypeError:", e)
class S(NamedTuple):
    a: int
    def total(self):
        return self.a + 1
    label = "s"
print(S(4).total(), S.label, S(4)._asdict())
