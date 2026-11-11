# A named tuple has no __dict__ (__slots__ is empty).
from typing import NamedTuple
class P(NamedTuple):
    x: int
p = P(1)
try:
    p.__dict__
except AttributeError as e:
    print("AttributeError:", e)
