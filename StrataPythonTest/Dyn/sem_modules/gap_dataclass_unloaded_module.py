# A dataclass whose __module__ names no loaded module.
from dataclasses import dataclass
@dataclass
class P:
    __module__ = "nowhere"
    x: int
