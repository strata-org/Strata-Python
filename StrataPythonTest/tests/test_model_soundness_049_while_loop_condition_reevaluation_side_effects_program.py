# While loop condition re-evaluation with object mutation — value semantics
# means condition never changes, causing non-termination
"""
A while loop condition that calls a method on an object is re-evaluated
each iteration in CPython. If the method mutates the object (e.g., a
counter that decrements), the condition depends on the CURRENT state.
In the value model, the object passed to the method is a copy — mutations
inside the method don't propagate back, so the condition never changes
and the loop either never executes or never terminates.
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def decrement(self: "Counter") -> int:
        self.value = self.value - 1
        return self.value

    def is_positive(self: "Counter") -> bool:
        return self.value > 0


def drain(c: Counter) -> int:
    total: int = 0
    while c.is_positive():
        total = total + c.value
        c.value = c.value - 1
    # CPython: c.value mutates in place, loop terminates
    # Model: c is value-typed, c.value never changes from caller's view,
    #         loop condition is always True (infinite loop) or always False
    return total


def countdown_sum(n: int) -> int:
    c: Counter = Counter(value=n)
    return drain(c)


def main() -> None:
    # countdown_sum(3): 3 + 2 + 1 = 6
    result: int = countdown_sum(3)
    assert result == 6

    # countdown_sum(0): loop never executes
    result2: int = countdown_sum(0)
    assert result2 == 0

    print(result, result2)


main()
