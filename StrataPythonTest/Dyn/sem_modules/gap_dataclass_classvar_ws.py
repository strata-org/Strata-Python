# A str annotation typing.ClassVar with whitespace around the dot.
import typing
from dataclasses import dataclass
@dataclass
class C:
    x: "typing\x0b.ClassVar" = 1
print(C())
