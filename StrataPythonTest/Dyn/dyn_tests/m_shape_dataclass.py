# Declared shapes of dataclasses: the decorators, bare or called with their arguments, and
# every annotated name with its default, ClassVar, InitVar and KW_ONLY included.
import dataclasses
from dataclasses import InitVar, KW_ONLY, dataclass
from typing import ClassVar


@dataclass
class P:
    x: int
    y: int = 0


@dataclasses.dataclass(frozen=True, order=False)
class Q:
    count: ClassVar[int] = 0
    seed: InitVar[int]
    _: KW_ONLY
    name: str = "q"
