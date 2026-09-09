# Method self not rebound to caller — mutating self in method is invisible to
# caller; must return modified instance or reject pattern
"""
When a method modifies `self` (writes to self.field), the caller's
variable is NOT updated under value semantics. The method operates on
a COPY of the object.

    obj.method()  # method modifies self internally
    # obj is UNCHANGED from caller's perspective

In CPython, obj IS modified (reference semantics). Under value semantics,
the caller must capture the return value:

    obj = obj.method()  # method returns modified self

Finding 011 identified this. Finding 098 identified self-rebinding within
the method. This finding focuses on the CALLER SIDE: even if the method
correctly rebinds self internally, the caller's variable is still the
old copy unless the method returns the new self AND the caller rebinds.

Uses ONLY confirmed-accepted constructs: @dataclass, method, int.
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def increment(self: "Counter") -> "Counter":
        """Correct pattern: return new instance."""
        return Counter(value=self.value + 1)

    def increment_wrong(self: "Counter") -> None:
        """Wrong pattern: modify self, return None."""
        self.value = self.value + 1
        # Under value semantics: self is rebound locally
        # But caller never sees this — self is a local copy!


def caller_rebinds() -> int:
    """Correct: capture return value."""
    c: Counter = Counter(value=0)
    c = c.increment()
    c = c.increment()
    c = c.increment()
    return c.value  # 3


def caller_forgets() -> int:
    """Wrong: doesn't capture return. Under value semantics, c unchanged."""
    c: Counter = Counter(value=0)
    c.increment()  # return value discarded!
    c.increment()  # return value discarded!
    c.increment()  # return value discarded!
    # CPython: c.value is still 0 (increment returns new, doesn't mutate)
    # Wait — increment() returns a NEW Counter, doesn't mutate self
    # So even in CPython, c is unchanged! This is correct.
    return c.value  # 0 (correct in both CPython and model)


def mutating_method_diverges() -> int:
    """increment_wrong modifies self — diverges between CPython and model."""
    c: Counter = Counter(value=0)
    c.increment_wrong()
    # CPython: c.value is 1 (self IS c, mutation visible)
    # Model: c.value is 0 (self is a copy, mutation lost)
    return c.value


def main() -> None:
    # Correct pattern
    assert caller_rebinds() == 3

    # Discarding return of non-mutating method — same in both
    assert caller_forgets() == 0

    # Mutating method — DIVERGES
    # CPython: 1 (mutation visible through reference)
    # Model: 0 (mutation lost — self is a copy)
    val: int = mutating_method_diverges()
    # In CPython this is 1, in model this is 0
    # The subset should REJECT this pattern

    print(caller_rebinds(), caller_forgets(), val)


main()
