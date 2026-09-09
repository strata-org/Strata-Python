# `True == 1` → `True`; PEq(from_bool, from_int) has no case → Hole; must
# normalize bool to int before comparison
"""
BOOL EQUALS INT — CROSS-TAG EQUALITY

DIVERGENCE:
  CPython:  True == 1   → True
  Model:    PEq(from_bool(True), from_int(1)) → Hole (no cross-tag case)

  CPython:  False == 0  → True
  Model:    PEq(from_bool(False), from_int(0)) → Hole

  CPython:  True == 2   → False
  Model:    PEq(from_bool(True), from_int(2)) → Hole

The model's PEq only handles same-tag pairs:
  (from_int, from_int) → compare ints
  (from_bool, from_bool) → compare bools
  (from_bool, from_int) → NO CASE → Hole
"""


def bool_eq_int() -> list[bool]:
    """Cross-tag equality between bool and int."""
    return [
        True == 1,    # CPython: True.  Model: Hole
        False == 0,   # CPython: True.  Model: Hole
        True == 2,    # CPython: False. Model: Hole
        False == 1,   # CPython: False. Model: Hole
    ]


def count_true(flags: list[bool]) -> int:
    """Sum bools — relies on True==1 for arithmetic."""
    total: int = 0
    for f in flags:
        if f == True:
            total += 1
    return total


def main() -> None:
    results: list[bool] = bool_eq_int()
    # CPython: [True, True, False, False]
    # Model: [Hole, Hole, Hole, Hole]
    assert results[0] == True   # True == 1
    assert results[1] == True   # False == 0
    assert results[2] == False  # True != 2
    assert results[3] == False  # False != 1

    assert count_true([True, False, True, True]) == 3

    print("all passed")


main()
