# A dataclass exception: its own __init__ comes before the built-in base.
from dataclasses import dataclass
@dataclass
class E(Exception):
    x: int
print(E.__doc__, E(1))
