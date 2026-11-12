# dataclass(weakref_slot=True) is not modelled.
from dataclasses import dataclass
@dataclass(weakref_slot=True)
class P:
    x: int
