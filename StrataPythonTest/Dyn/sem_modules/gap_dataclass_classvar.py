# typing.ClassVar is not modelled, in a str annotation too.
import typing
from dataclasses import dataclass
@dataclass
class P:
    x: int
    y: "typing.ClassVar" = 0
