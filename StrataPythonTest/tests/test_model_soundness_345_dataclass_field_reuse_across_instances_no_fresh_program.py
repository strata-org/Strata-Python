# Dataclass default field across instances — each construction must inline
# fresh default; shared variable would break independence
"""
DATACLASS FIELD DEFAULT LIST/DICT — SHARED MUTABLE STATE ACROSS INSTANCES

CPython: @dataclass with `field(default_factory=list)` creates a FRESH list
         per instance. But if someone writes `items: list[int] = []` without
         field(), CPython's generated __init__ uses the SAME list object
         for all instances (shared mutable default).

         However, the subset bans mutable defaults ("No mutable default
         arguments"). So this specific bug is OUT.

         BUT: even with field(default_factory=list), the model must ensure
         each construction produces a FRESH empty list — not a shared one.
         Under value semantics this is AUTOMATICALLY CORRECT (no aliasing).

         The ACTUAL gap: when a dataclass has a field with a default value
         that is a PRIMITIVE (e.g., `count: int = 0`), and two instances
         are created, the model must prove they are INDEPENDENT.
         Under value semantics this works. But if the translator reuses
         a single symbolic variable for the default, both instances
         share the same SMT variable — modifications to one affect the other.

This tests that the model correctly produces INDEPENDENT instances
even when constructed with the same default values.
"""
from dataclasses import dataclass


@dataclass
class Counter:
    name: str
    count: int = 0


def increment(c: Counter) -> Counter:
    return Counter(c.name, c.count + 1)


def main() -> None:
    # Create two counters with same defaults
    a: Counter = Counter("alpha")
    b: Counter = Counter("beta")

    # They start equal in count
    assert a.count == 0
    assert b.count == 0

    # Modify one — the other must be unaffected
    a2: Counter = increment(a)

    # CPython: a2.count == 1, b.count == 0 (independent)
    # Model risk: if translator uses single variable for default 0,
    #   and increment modifies "the" default variable, b.count changes too
    assert a2.count == 1
    assert b.count == 0  # MUST still be 0

    # Original a is also unchanged (value semantics)
    assert a.count == 0

    # Create more instances — all independent
    c: Counter = Counter("gamma")
    c2: Counter = increment(increment(c))
    assert c2.count == 2
    assert a.count == 0
    assert b.count == 0

    # Test with non-zero initial value
    d: Counter = Counter("delta", 10)
    e: Counter = Counter("epsilon", 10)
    d2: Counter = increment(d)
    assert d2.count == 11
    assert e.count == 10  # independent despite same initial value

    print("all passed")


main()
