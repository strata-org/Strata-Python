# `bool([])` → `False`; Any_to_bool has no from_ListAny case → Hole; empty
# list is falsy, non-empty is truthy
"""
EMPTY LIST TRUTHINESS IS FALSE

DIVERGENCE:
  CPython:  bool([])     → False
  Model:    Any_to_bool(from_ListAny(nil)) → Hole (finding 322)

  CPython:  bool([1,2])  → True
  Model:    Any_to_bool(from_ListAny(cons(...))) → Hole

  CPython:  if []: print("yes") → never prints
  Model:    if Hole: → non-deterministic (solver picks either branch)

Empty containers are falsy in Python. The model's Any_to_bool has
no case for from_ListAny — it returns Hole, making conditions
on lists non-deterministic.
"""


def is_empty(xs: list[int]) -> bool:
    """Check emptiness via truthiness."""
    if xs:
        return False
    return True


def first_or_default(xs: list[int], default: int) -> int:
    """Common pattern: use list truthiness as guard."""
    if xs:
        return xs[0]
    return default


def process_if_nonempty(xs: list[int]) -> int:
    """Only process non-empty lists."""
    if not xs:
        return 0
    total: int = 0
    for x in xs:
        total += x
    return total


def main() -> None:
    # CPython: [] is falsy → is_empty returns True
    # Model: Any_to_bool(from_ListAny(nil)) → Hole → non-deterministic
    assert is_empty([]) == True
    assert is_empty([1]) == False
    assert is_empty([1, 2, 3]) == False

    # First or default
    assert first_or_default([10, 20], -1) == 10
    assert first_or_default([], -1) == -1

    # Process if nonempty
    assert process_if_nonempty([1, 2, 3]) == 6
    assert process_if_nonempty([]) == 0

    # Direct truthiness
    assert not []
    assert [1]

    print("all passed")


main()
