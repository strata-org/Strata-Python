import dataclasses
import dataclasses as dc_module
from dataclasses import dataclass
from dataclasses import dataclass as dc


@dataclass
class Point:
    x: int
    y: int


@dataclasses.dataclass()
class Box:
    w: int
    h: int


@dc
class Size:
    width: int
    height: int


@dc_module.dataclass()
class Position:
    x: int
    y: int
