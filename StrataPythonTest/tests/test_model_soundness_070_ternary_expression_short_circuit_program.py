# Ternary expression (`a if cond else b`) evaluates both arms eagerly — side
# effects in unselected arm execute
"""
Python's ternary expression `a if cond else b` evaluates ONLY ONE of
`a` or `b` depending on the truthiness of `cond`. If the model evaluates
both arms eagerly (like a function call `select(cond, a, b)`), side
effects in the unselected arm execute incorrectly.

This is the expression-level analog of finding 044 (short-circuit and/or).
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def bump(self: "Counter") -> int:
        self.value = self.value + 1
        return self.value


def safe_divide(x: int, y: int) -> int:
    # If y == 0, the division is never evaluated
    return x // y if y != 0 else 0


def pick_with_effect(flag: bool, c: Counter) -> int:
    # Only one branch's side effect should execute
    return c.bump() if flag else 0


def nested_ternary(x: int) -> str:
    return "positive" if x > 0 else ("negative" if x < 0 else "zero")


def main() -> None:
    # Safe division: y=0 doesn't crash
    assert safe_divide(10, 2) == 5
    assert safe_divide(10, 0) == 0  # Model (eager): 10 // 0 crashes

    # Side effect only in selected branch
    c: Counter = Counter(value=0)
    r1: int = pick_with_effect(True, c)
    # CPython: bump() called, c.value=1, returns 1
    assert r1 == 1
    assert c.value == 1

    r2: int = pick_with_effect(False, c)
    # CPython: bump() NOT called, c.value stays 1, returns 0
    assert r2 == 0
    assert c.value == 1  # Model (eager): c.value == 2

    # Nested ternary
    assert nested_ternary(5) == "positive"
    assert nested_ternary(-3) == "negative"
    assert nested_ternary(0) == "zero"

    print(r1, r2, c.value)


main()
