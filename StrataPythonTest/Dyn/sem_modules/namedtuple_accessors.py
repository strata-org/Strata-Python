# The field accessors: their __get__, __set__, __delete__ and repr, and their errors.
from typing import NamedTuple
class P(NamedTuple):
    x: int
    y: int = 0
p = P(1)
g = P.x
for f in (lambda: g.__get__(), lambda: g.__get__(None), lambda: g.__get__(p, P, 3), lambda: g.__set__(p),
          lambda: g.__delete__(), lambda: g.__get__(p, w=1), lambda: g.__repr__(1), lambda: type(g).__get__(5, p),
          lambda: g.__get__(()), lambda: P.y.__get__((1,)), lambda: g.__get__(None, None), lambda: g.__get__(None, 5),
          lambda: g.__get__([1]), lambda: g.__get__(5, None)):
    try:
        print(f())
    except (TypeError, IndexError, AttributeError) as e:
        print(type(e).__name__ + ":", e)
print(repr(g), g, P.y)
