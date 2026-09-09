# Value sem: method mutates self caller unchanged — `c.increment_wrong()`
# modifies copy of self; CPython: c.value==3, Model: c.value==0
"""
VALUE SEMANTICS WHERE CPYTHON HAS REFERENCE SEMANTICS:
Method mutates self (writes to self.field) — caller's variable unchanged.

CPython: self IS the caller's object. self.x = v mutates it.
Model: self is a COPY. self.x = v rebuilds the copy. Caller unchanged.

CPython result: counter.value == 3
Model result:  counter.value == 0
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def increment_wrong(self: "Counter") -> None:
        """WRONG pattern: mutates self, returns None."""
        self.value = self.value + 1

    def increment_right(self: "Counter") -> "Counter":
        """RIGHT pattern: returns new Counter."""
        return Counter(value=self.value + 1)


def wrong_usage() -> int:
    """Caller doesn't see self-mutation."""
    c: Counter = Counter(value=0)
    c.increment_wrong()
    c.increment_wrong()
    c.increment_wrong()
    # CPython: c.value == 3 (self IS c, mutation visible)
    # Model:  c.value == 0 (self is copy, mutation lost)
    return c.value


def right_usage() -> int:
    """Caller rebinds — works in both."""
    c: Counter = Counter(value=0)
    c = c.increment_right()
    c = c.increment_right()
    c = c.increment_right()
    return c.value  # 3 in BOTH


def main() -> None:
    assert wrong_usage() == 3  # True in CPython
    assert right_usage() == 3  # True in both

    print(wrong_usage(), right_usage())


main()
