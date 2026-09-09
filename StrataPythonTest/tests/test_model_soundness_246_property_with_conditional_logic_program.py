# @property with conditional logic — getter body has if/else; must translate
# as function call; property-calls-property needs resolution
"""
@property with conditional logic in the getter. The property body
contains if/else, field reads, and arithmetic — all IN the subset.
The frontend accepts this (no unsupported construct). But the model
must translate property access as a function call (finding 222).

The conditional logic inside the property means the return value
depends on field state — the model must inline or summarize correctly.

All constructs used: @dataclass, @property, if/else, int, comparison.
"""
from dataclasses import dataclass


@dataclass
class Battery:
    capacity: int
    current: int

    @property
    def percentage(self: "Battery") -> int:
        if self.capacity == 0:
            return 0
        return (self.current * 100) // self.capacity

    @property
    def status(self: "Battery") -> int:
        """0=empty, 1=low, 2=medium, 3=full."""
        pct: int = self.percentage
        if pct == 0:
            return 0
        if pct < 20:
            return 1
        if pct < 80:
            return 2
        return 3

    @property
    def is_critical(self: "Battery") -> bool:
        return self.percentage < 10


def check_battery() -> int:
    b: Battery = Battery(capacity=100, current=75)
    return b.percentage  # 75


def status_check() -> int:
    b: Battery = Battery(capacity=200, current=30)
    return b.status  # 30*100//200 = 15 → status 1 (low)


def critical_check() -> bool:
    b: Battery = Battery(capacity=100, current=5)
    return b.is_critical  # 5 < 10 → True


def property_calls_property() -> int:
    """status calls percentage — nested property access."""
    b: Battery = Battery(capacity=100, current=90)
    return b.status  # 90% → status 3 (full)


def main() -> None:
    assert check_battery() == 75
    assert status_check() == 1
    assert critical_check() == True
    assert property_calls_property() == 3

    b: Battery = Battery(capacity=0, current=0)
    assert b.percentage == 0  # division guard

    print(check_battery(), status_check(), property_calls_property())


main()
