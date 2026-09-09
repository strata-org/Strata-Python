# `@classmethod` has no `self` — translator must not pass ClassInstance; `cls`
# parameter should be erased
"""
@classmethod receives `cls` (the class itself) instead of `self` (an
instance). It can create new instances but has no instance state.
The model must handle classmethod calls differently from instance methods:
- No `self` parameter (no ClassInstance passed)
- `cls` is the class type, not an instance
- Can call cls(...) to construct new instances

If the translator treats classmethod like instance method, it may
pass a ClassInstance as the first argument (wrong).
"""
from dataclasses import dataclass


@dataclass
class Temperature:
    celsius: float

    @classmethod
    def from_fahrenheit(cls, f: float) -> "Temperature":
        return Temperature(celsius=(f - 32.0) * 5.0 / 9.0)

    @classmethod
    def freezing(cls) -> "Temperature":
        return Temperature(celsius=0.0)

    @classmethod
    def boiling(cls) -> "Temperature":
        return Temperature(celsius=100.0)

    def to_fahrenheit(self: "Temperature") -> float:
        return self.celsius * 9.0 / 5.0 + 32.0


@dataclass
class Vector:
    x: float
    y: float

    @classmethod
    def zero(cls) -> "Vector":
        return Vector(x=0.0, y=0.0)

    @classmethod
    def unit_x(cls) -> "Vector":
        return Vector(x=1.0, y=0.0)


def main() -> None:
    # Classmethod as factory
    t1: Temperature = Temperature.from_fahrenheit(212.0)
    assert t1.celsius == 100.0

    t2: Temperature = Temperature.freezing()
    assert t2.celsius == 0.0

    t3: Temperature = Temperature.boiling()
    assert t3.to_fahrenheit() == 212.0

    # Vector factories
    v: Vector = Vector.zero()
    assert v.x == 0.0
    assert v.y == 0.0

    u: Vector = Vector.unit_x()
    assert u.x == 1.0

    print(t1.celsius, t2.celsius, v.x)


main()
