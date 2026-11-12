# A dataclass whose metaclass is not type.
from dataclasses import dataclass
class M(type):
    pass
@dataclass
class P(metaclass=M):
    x: int
