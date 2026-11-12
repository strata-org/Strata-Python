# The docstring of a dataclass with a built-in base.
from dataclasses import dataclass
@dataclass(init=False)
class E(Exception):
    x: int = 0
print(E.__doc__)
@dataclass(init=False)
class L(list):
    x: int = 0
print(L.__doc__)
