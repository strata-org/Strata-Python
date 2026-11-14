# entries: collections._tuplegetter.__set__
from typing import NamedTuple
class P(NamedTuple):
    x: int
p = P(1)
try:
    p.x = 2
except AttributeError as e:
    print(type(e).__name__, e)
print(P.x.__get__(None, P) is P.x, P.x.__doc__)
