from dataclasses import dataclass


@dataclass
class Plain:
    a: int


@dataclass(order=True)
class Ordered:
    b: int
