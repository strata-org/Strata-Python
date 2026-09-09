# `and`/`or` short-circuit — if translator evaluates both operands eagerly,
# side-effecting RHS executes when LHS determines result
"""
Python's `and` and `or` are short-circuit operators: `a and b` does NOT
evaluate `b` if `a` is falsy; `a or b` does NOT evaluate `b` if `a` is
truthy. If the Laurel translator emits both operands eagerly (e.g., as
PAnd(eval(a), eval(b))), side-effecting function calls on the RHS execute
unconditionally, diverging from CPython.
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def increment(self: "Counter") -> bool:
        self.value = self.value + 1
        return True


def check_and_skip(flag: bool, c: Counter) -> bool:
    # CPython: if flag is False, c.increment() is NEVER called
    # Model (eager): c.increment() is always called
    return flag and c.increment()


def check_or_skip(flag: bool, c: Counter) -> bool:
    # CPython: if flag is True, c.increment() is NEVER called
    # Model (eager): c.increment() is always called
    return flag or c.increment()


def guarded_division(x: int, y: int) -> bool:
    # Classic guard pattern: y != 0 prevents division by zero
    # CPython: if y == 0, (x // y == 0) is never evaluated
    # Model (eager): x // y is evaluated even when y == 0
    return y != 0 and x // y == 0


def main() -> None:
    c1: Counter = Counter(value=0)
    r1: bool = check_and_skip(False, c1)
    # CPython: r1 = False, c1.value = 0 (increment never called)
    assert r1 == False
    assert c1.value == 0  # Model (eager): c1.value == 1

    c2: Counter = Counter(value=0)
    r2: bool = check_or_skip(True, c2)
    # CPython: r2 = True, c2.value = 0 (increment never called)
    assert r2 == True
    assert c2.value == 0  # Model (eager): c2.value == 1

    # Guard pattern: should not crash
    r3: bool = guarded_division(10, 0)
    # CPython: r3 = False (short-circuits, no division)
    # Model (eager): evaluates 10 // 0, raises ZeroDivisionError or Hole
    assert r3 == False

    print(r1, c1.value, r2, c2.value, r3)


main()
