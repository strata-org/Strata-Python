# The __repr__ that dataclass generates is CPython's _recursive_repr wrapper, whose functools.wraps
# __dict__ holds __wrapped__: reading it stops with a gap.
from dataclasses import dataclass
@dataclass
class P:
    x: int
try:
    P.__repr__.__wrapped__
    print("has __wrapped__")
except AttributeError as e:
    print("AttributeError:", e)
