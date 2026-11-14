from dataclasses import dataclass
@dataclass
class D:
    a: int
    __post_init__ = None
try:
    print(D(1))
except TypeError as e:
    print(type(e).__name__, e)
