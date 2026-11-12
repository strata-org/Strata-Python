# dataclass(slots=True) is not modelled.
from dataclasses import dataclass
@dataclass(slots=True)
class P:
    x: int
