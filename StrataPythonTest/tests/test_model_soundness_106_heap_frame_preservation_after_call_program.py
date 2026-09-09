# Heap frame preservation — after `a.method()`, unrelated object `b` must
# retain its field values
"""
After calling a method on one object, other objects on the heap must
be UNCHANGED (heap frame preservation). If the verifier doesn't know
that `a.method()` only modifies `a`, it may assume `b` was also
modified — losing all knowledge about `b`'s fields.

This is the multi-object version of finding 103. The frame rule says:
"objects not mentioned in the modifies clause retain their values."
"""
from dataclasses import dataclass


@dataclass
class Counter:
    name: str
    value: int

    def increment(self: "Counter") -> None:
        self.value = self.value + 1


def independent_counters() -> bool:
    """Two counters are independent — modifying one preserves the other."""
    a: Counter = Counter(name="hits", value=0)
    b: Counter = Counter(name="errors", value=0)

    a.increment()
    a.increment()
    a.increment()

    # After modifying a, b must be unchanged
    # Without heap frame: b.value could be anything (havoc'd)
    return b.value == 0 and a.value == 3


def modify_first_preserve_second(x: Counter, y: Counter) -> int:
    """Modify x, return y's value (must be preserved)."""
    saved: int = y.value
    x.increment()
    x.increment()
    # y.value must still equal saved
    return y.value


def main() -> None:
    # Independent counters
    assert independent_counters() == True

    # Modify one, preserve other
    c1: Counter = Counter(name="a", value=10)
    c2: Counter = Counter(name="b", value=20)
    result: int = modify_first_preserve_second(c1, c2)
    assert result == 20  # c2 unchanged
    assert c1.value == 12  # c1 incremented twice

    print(independent_counters(), result, c1.value)


main()
