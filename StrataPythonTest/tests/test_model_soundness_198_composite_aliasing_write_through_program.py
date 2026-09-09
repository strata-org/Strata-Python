# Composite aliasing write-through — `b = a; a.x = 99` visible through b;
# subset MUST reject this pattern for ClassInstance soundness
"""
Under Composite/heap semantics, aliasing is possible:
    a = MyClass(x=1)
    b = a  # b aliases a (same heap reference)
    a.x = 99
    # b.x is also 99 (same object)

This is the REASON Composite exists — to model aliasing that
ClassInstance (value semantics) cannot handle.

The Frontend subset says "no aliasing" for v1, so this pattern is OUT.
But if the subset is expanded, Composite must handle write-through:
modifying through one alias must be visible through all other aliases.

This finding documents what Composite MUST support if aliasing is added,
and verifies that the current subset correctly REJECTS these patterns.

Uses ONLY confirmed-accepted constructs: @dataclass, int.
(NOTE: This program demonstrates patterns that SHOULD be rejected by
the subset checker. It runs in CPython but would be OUT of Frontend.)
"""
from dataclasses import dataclass


@dataclass
class Shared:
    value: int


def alias_write_through() -> bool:
    """Aliasing: write through one reference visible through other.
    THIS PATTERN IS OUT OF SUBSET (no aliasing rule)."""
    a: Shared = Shared(value=1)
    b: Shared = a  # alias! (OUT of subset)
    a.value = 99
    # CPython: b.value is 99 (same object)
    # Value model: b.value is 1 (copy at assignment time)
    return b.value == 99  # True in CPython, False in value model


def no_alias_correct() -> bool:
    """Non-aliasing: separate objects, independent.
    THIS PATTERN IS IN SUBSET."""
    a: Shared = Shared(value=1)
    b: Shared = Shared(value=1)  # separate construction, not alias
    a = Shared(value=99)
    # b is unchanged
    return b.value == 1  # True in both CPython and model


def function_param_alias() -> bool:
    """Passing object to function creates alias in CPython.
    THIS PATTERN IS OUT OF SUBSET (mutation through param)."""
    def modify(obj: Shared) -> None:
        obj.value = 42

    s: Shared = Shared(value=0)
    modify(s)
    # CPython: s.value is 42 (obj aliases s)
    # Value model: s.value is 0 (obj is a copy)
    return s.value == 42  # True in CPython, False in value model


def main() -> None:
    # Aliasing pattern (OUT of subset — demonstrates divergence)
    alias_result: bool = alias_write_through()
    # In CPython: True. In value model: would be False.
    assert alias_result == True  # CPython behavior

    # Non-aliasing (IN subset — correct in both)
    assert no_alias_correct() == True

    # Function param alias (OUT of subset)
    param_result: bool = function_param_alias()
    assert param_result == True  # CPython behavior

    print(alias_result, no_alias_correct(), param_result)


main()
