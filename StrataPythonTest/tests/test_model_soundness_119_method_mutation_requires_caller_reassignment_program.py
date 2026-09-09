# Method mutation requires caller reassignment — `s.push(10)` without `s =
# s.push(10)` loses the mutation
"""
Under value semantics, a method that modifies self produces a new value
internally, but the CALLER's variable still holds the old value. The
caller must reassign: `obj = obj.method()` (if method returns self) or
the method must return the modified value explicitly.

This is the "caller must reassign" pattern that value semantics forces.
Programs that call mutating methods without reassignment silently lose
the mutations.
"""
from dataclasses import dataclass


@dataclass
class Stack:
    items: list[int]
    size: int

    def push(self: "Stack", value: int) -> "Stack":
        self.items = self.items + [value]
        self.size = self.size + 1
        return self

    def pop(self: "Stack") -> tuple[int, "Stack"]:
        # Can't actually return tuple (finding 028), so simulate
        # In practice: modifies self, returns popped value
        top: int = self.items[self.size - 1]
        self.size = self.size - 1
        return top  # type: ignore


def correct_usage() -> int:
    """Caller reassigns after each mutation — works under value semantics."""
    s: Stack = Stack(items=[], size=0)
    s = s.push(10)  # reassign!
    s = s.push(20)  # reassign!
    s = s.push(30)  # reassign!
    return s.size


def incorrect_usage() -> int:
    """Caller does NOT reassign — mutations lost under value semantics."""
    s: Stack = Stack(items=[], size=0)
    s.push(10)  # no reassignment — return value discarded
    s.push(20)  # same
    s.push(30)  # same
    # CPython: s.size == 3 (mutated in place)
    # Model: s.size == 0 (mutations lost)
    return s.size


def main() -> None:
    # Correct: reassign after each call
    assert correct_usage() == 3

    # Incorrect: no reassignment
    # CPython: still works (mutation in place)
    assert incorrect_usage() == 3  # CPython: 3, Model: 0

    print(correct_usage(), incorrect_usage())


main()
