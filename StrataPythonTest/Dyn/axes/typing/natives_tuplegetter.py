from typing import NamedTuple
class P(NamedTuple):
    x: int
p = P(1)
for f in (lambda: setattr(p, 'x', 2), lambda: delattr(p, 'x'), lambda: P.x.__get__(None, P) is P.x, lambda: P.x.__doc__, lambda: p.__getnewargs__()):
    try:
        print(f())
    except Exception as e:
        print(type(e).__name__, e)
