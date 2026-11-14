# entries: collections._tuplegetter.__delete__
from typing import NamedTuple
class P(NamedTuple):
    x: int
p = P(1)
try:
    del p.x
except AttributeError as e:
    print(type(e).__name__, e)
