# Well-behaved: frozen dataclasses read-only after construction and
# isinstance-guarded dispatch, the fragment's intended style. All sites
# devirtualize; no aborts.
from dataclasses import dataclass


@dataclass(frozen=True)
class Circle:
    r: float

    def area(self) -> float:
        return 3.14159 * self.r * self.r


@dataclass(frozen=True)
class Square:
    side: float

    def area(self) -> float:
        return self.side * self.side


def total_area(shapes: list) -> float:
    total = 0.0
    for s in shapes:
        if isinstance(s, Circle):
            total = total + s.area()
        elif isinstance(s, Square):
            total = total + s.area()
    return total


figures = [Circle(1.0), Square(2.0), Circle(0.5)]
t = total_area(figures)
