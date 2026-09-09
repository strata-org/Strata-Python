# Functional update pattern `obj = obj.method()` — POSITIVE: value semantics
# correctly models this pattern when caller rebinds
"""
FUNCTIONAL UPDATE PATTERN — CALLER MUST REBIND TO SEE CHANGES

CPython: obj.method() mutates obj in place. Caller sees changes.
Model:   method returns new ClassInstance. Caller must rebind.

The CORRECT pattern under value semantics:
    obj = obj.method()  # rebind to capture the new value

The INCORRECT pattern (works in CPython, fails in model):
    obj.method()  # mutation in place — caller sees it
    # Model: method returns new value, DISCARDED

This finding tests that the CORRECT functional pattern works:
methods that return a new instance, caller rebinds.
This is the SOUND usage pattern for from_ClassInstance.
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def increment(self: "Counter") -> "Counter":
        """Functional update: returns new Counter."""
        return Counter(self.value + 1)

    def add(self: "Counter", n: int) -> "Counter":
        return Counter(self.value + n)

    def reset(self: "Counter") -> "Counter":
        return Counter(0)


@dataclass
class Stack:
    items: list[int]
    size: int

    def push(self: "Stack", val: int) -> "Stack":
        new_items: list[int] = self.items + [val]
        return Stack(new_items, self.size + 1)

    def peek(self: "Stack") -> int:
        return self.items[self.size - 1]


def counter_usage() -> int:
    """Correct pattern: rebind after each method call."""
    c: Counter = Counter(0)
    c = c.increment()  # rebind!
    c = c.increment()  # rebind!
    c = c.add(5)       # rebind!
    return c.value


def counter_chain() -> int:
    """Chaining functional updates."""
    c: Counter = Counter(10)
    c = c.add(5)
    c = c.add(3)
    c = c.reset()
    c = c.increment()
    return c.value


def stack_usage() -> int:
    """Stack with functional push."""
    s: Stack = Stack([], 0)
    s = s.push(10)
    s = s.push(20)
    s = s.push(30)
    return s.peek()


def main() -> None:
    # Test 1: counter with rebinding
    assert counter_usage() == 7

    # Test 2: chain of operations
    assert counter_chain() == 1

    # Test 3: stack
    assert stack_usage() == 30

    # Test 4: original unchanged (value semantics)
    c: Counter = Counter(5)
    c2: Counter = c.increment()
    assert c.value == 5   # original unchanged
    assert c2.value == 6  # new value in c2

    print("all passed")


main()
