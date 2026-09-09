# `int(True)` must return `from_int(1)` not `from_bool(True)` — tag
# normalization required; without it `int(flag) + total` → Hole
"""
INT() CONVERSION ON BOOL — TAG NORMALIZATION MISSING

The subset allows:
  - int(x) for primitive-type conversions
  - bool values True/False
  - bool is a subclass of int in CPython

CPython behavior:
  int(True)  → 1  (type: int)
  int(False) → 0  (type: int)
  type(int(True)) → <class 'int'>  (NOT bool!)

Model behavior:
  int(True) → to_int_any(from_bool(True))
  
  If to_int_any has a from_bool case:
    → from_int(1)  ✓ correct
  If to_int_any has NO from_bool case (likely, per finding 017):
    → Hole  ✗ wrong

  Even if to_int_any handles from_bool, the CRITICAL question is:
  does it return from_int(1) or from_bool(True)?
  
  CPython: int(True) returns a TRUE INT (not a bool). The type changes.
  This matters for isinstance checks:
    isinstance(True, int)     → True  (bool IS int)
    isinstance(int(True), bool) → False  (int(True) is NOT bool!)
    type(True) == type(int(True)) → False

The model must:
1. Have a from_bool case in to_int_any
2. Return from_int (not from_bool) to reflect the type change
3. Map True→1, False→0

This is distinct from finding 017 (int() has no model at all) because
even WITH a model, the bool→int normalization must produce from_int
not from_bool. And it's distinct from finding 166 (bool arithmetic)
because here the user EXPLICITLY requests conversion via int().
"""


def bool_to_int_explicit(b: bool) -> int:
    """Explicit conversion — must return actual int, not bool."""
    return int(b)


def count_true_values(flags: list[bool]) -> int:
    """Count True values by converting each to int and summing."""
    total: int = 0
    for flag in flags:
        total = total + int(flag)
    return total


def bool_int_type_difference() -> bool:
    """After int(), the value is int not bool.
    
    CPython: int(True) + int(True) = 2 (int arithmetic)
    Model: if int(True) returns from_bool(True), then
           PAdd(from_bool(True), from_bool(True)) → Hole (no case)
           
    If int(True) correctly returns from_int(1), then
           PAdd(from_int(1), from_int(1)) → from_int(2) ✓
    """
    a: int = int(True)
    b: int = int(False)
    result: int = a + b  # Should be 1 + 0 = 1
    return result == 1


def weighted_sum(values: list[int], weights: list[bool]) -> int:
    """Multiply each value by its boolean weight (0 or 1).
    
    Pattern: value * int(weight) — requires int(bool) → from_int
    """
    total: int = 0
    i: int = 0
    while i < len(values) and i < len(weights):
        total = total + values[i] * int(weights[i])
        i = i + 1
    return total


def conditional_to_int(x: int) -> int:
    """Convert comparison result to int for arithmetic.
    
    Pattern: int(x > 0) gives 1 if positive, 0 otherwise.
    CPython: int(True) = 1, int(False) = 0
    Model: comparison returns from_bool, int() must normalize to from_int
    """
    positive: bool = x > 0
    return int(positive)


def main() -> None:
    # Basic conversion
    assert int(True) == 1
    assert int(False) == 0

    # Type is int, not bool (CPython behavior)
    # Note: we can't test type() directly in Frontend, but the TAG matters
    # for subsequent operations

    # Counting pattern
    assert count_true_values([True, False, True, True, False]) == 3
    assert count_true_values([]) == 0
    assert count_true_values([False, False]) == 0

    # Arithmetic after conversion
    assert bool_int_type_difference() == True

    # Weighted sum
    assert weighted_sum([10, 20, 30], [True, False, True]) == 40
    assert weighted_sum([5, 5, 5], [True, True, True]) == 15

    # Conditional to int
    assert conditional_to_int(5) == 1
    assert conditional_to_int(-3) == 0
    assert conditional_to_int(0) == 0

    print(int(True), int(False), count_true_values([True, True, False]))


main()
