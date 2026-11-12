# A dataclass with __abstractmethods__.
from dataclasses import dataclass
@dataclass
class P:
    __abstractmethods__ = ()
    x: int
