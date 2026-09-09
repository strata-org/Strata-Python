# `field(default_factory=list)` in @dataclass — translator must recognize
# `field()` sentinel and substitute factory result at construction; without
# it, field is Hole or wrong type
"""
DATACLASS field_default FACTORY (field(default_factory=list)) — SHARED STATE

The subset allows:
  - @dataclass (IN)
  - list fields (IN)
  - Default values for fields (IN)
  - `from dataclasses import dataclass, field` (IN — dataclass imports)

The NOVEL gap: `field(default_factory=list)` creates a FRESH list for
each instance. But the model has no concept of default_factory — it
either:
  1. Treats the default as a LITERAL [] shared across instances (WRONG:
     CPython creates fresh list per instance via factory call)
  2. Ignores the default entirely (field is Hole if not passed)
  3. Inlines [] as a constant (CORRECT for value semantics, but only
     if the translator recognizes `field(default_factory=...)`)

The CRITICAL distinction from finding 345 (dataclass field reuse):
  - Finding 345 is about MUTABLE defaults like `items: list[int] = []`
    which is a PYTHON BUG (shared mutable default)
  - THIS finding is about `field(default_factory=list)` which is the
    CORRECT pattern — each instance gets a fresh list

Under value semantics, both patterns are actually SOUND (no aliasing),
but the translator must RECOGNIZE `field(default_factory=...)` syntax
and substitute a fresh empty list at each construction site.

If the translator doesn't handle `field()`:
  - The field has no default → construction without that arg fails
  - Or the field gets `field(default_factory=list)` as its VALUE
    (the field() call object, not an empty list) → type mismatch

ROOT CAUSE: `field(default_factory=list)` is a CALL EXPRESSION in the
class body that the @dataclass decorator interprets at class-creation
time. The translator must recognize this pattern and emit the factory
call (or its result) at each construction site.
"""
from dataclasses import dataclass, field


@dataclass
class Counter:
    name: str
    counts: list[int] = field(default_factory=list)

    def increment(self: "Counter", value: int) -> "Counter":
        new_counts: list[int] = self.counts + [value]
        return Counter(name=self.name, counts=new_counts)


def main() -> None:
    # Construction without explicit counts — uses default_factory
    c1: Counter = Counter(name="alpha")
    c2: Counter = Counter(name="beta")

    # CPython: c1.counts is [] (fresh list from factory)
    # CPython: c2.counts is [] (DIFFERENT fresh list from factory)
    assert c1.counts == []
    assert c2.counts == []

    # Model risk 1: if field(default_factory=list) not recognized,
    #   Counter("alpha") fails (missing required arg 'counts')
    # Model risk 2: if treated as shared default,
    #   c1.counts and c2.counts are same object (but under value
    #   semantics this is actually fine — no aliasing)
    # Model risk 3: if field() call stored as value,
    #   c1.counts is field(default_factory=list) object, not []

    # Use the counter
    c1_v2: Counter = c1.increment(10)
    assert c1_v2.counts == [10]
    assert c1.counts == []  # Original unchanged (value semantics correct here)

    # Multiple instances with defaults are independent
    c3: Counter = Counter(name="gamma")
    c3_v2: Counter = c3.increment(99)
    assert c3_v2.counts == [99]
    assert c1.counts == []  # c1 unaffected

    print("all assertions passed")


main()
