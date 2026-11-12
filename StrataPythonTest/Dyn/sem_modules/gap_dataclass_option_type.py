# An option that is not a bool.
from dataclasses import dataclass
@dataclass(eq=1)
class P:
    x: int
