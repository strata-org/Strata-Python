# A class body that takes another dataclass's __init__.
from dataclasses import dataclass
@dataclass
class O:
    q: int
@dataclass(init=False)
class C:
    __init__ = O.__init__
    x: str = "a"
print(C.__doc__)
