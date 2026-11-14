from dataclasses import dataclass, field
def mk(cls):
    return 9
@dataclass
class D:
    a: int = field(default_factory=classmethod(mk))
try:
    print(D())
except TypeError as e:
    print(type(e).__name__, e)
