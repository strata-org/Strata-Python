# A default that passes for a Field through __class__.
from dataclasses import dataclass, Field, MISSING
class Fake:
    @property
    def __class__(self):
        return Field
    kw_only = False
    default = 5
    default_factory = MISSING
    init = True
    repr = True
    compare = True
    hash = None
@dataclass
class C:
    x: int = Fake()
print(C(), C.x)
