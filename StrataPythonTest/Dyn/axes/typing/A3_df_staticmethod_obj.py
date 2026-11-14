from dataclasses import dataclass, field
def mk():
    return 9
@dataclass
class D:
    a: int = field(default_factory=staticmethod(mk))
print(D())
