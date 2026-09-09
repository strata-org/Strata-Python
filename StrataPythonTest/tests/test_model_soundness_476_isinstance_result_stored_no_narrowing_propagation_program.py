# isinstance result stored in variable — narrowing only triggers on direct `if
# isinstance(x,T):` pattern; stored `flag = isinstance(x,T); if flag:` has no
# narrowing
"""
ISINSTANCE RESULT STORED IN VARIABLE — NARROWING DOESN'T PROPAGATE

The subset allows:
  - isinstance(x, T) for narrowing (IN)
  - Boolean variables (IN)
  - if/else with boolean condition (IN)
  - Optional[T] types (IN)

The NOVEL gap: isinstance narrowing only works when the isinstance call
appears DIRECTLY in the if-condition. Storing the result in a boolean
variable and using that variable later does NOT trigger narrowing.

CPython behavior:
  - `flag = isinstance(x, int); if flag: x + 1` — works fine (x IS int)
  - The isinstance check is TRUE, so x is definitely int in the branch

Model behavior:
  - `flag = isinstance(x, int)` → flag gets from_bool(True/False)
  - `if flag:` → enters branch, but NO assume(isfrom_int(x)) emitted
  - `x + 1` → PAdd(x, from_int(1)) where x has tag {from_int, from_None}
  - Result: Hole or verification failure (can't prove x is int)

The narrowing mechanism in the translator recognizes the PATTERN:
    if isinstance(x, T):
        # x is narrowed to T here

But does NOT recognize:
    flag = isinstance(x, T)
    if flag:
        # x is NOT narrowed (flag is just a bool variable)

This is a semantic gap: the translator performs pattern-matching on the
AST of the if-condition, not dataflow analysis.

DISTINCT FROM:
  - Finding 245 (comparison result stored) — that's about PLt/PGt
    return type; this is about NARROWING not propagating
  - Finding 334 (narrowing killed by else assign) — that's about
    narrowing being invalidated; this is about narrowing never starting
  - Finding 464 (narrowing at loop back-edge) — that's about loop
    iteration; this is about variable indirection
"""
from typing import Optional


def direct_isinstance_works(x: Optional[int]) -> int:
    """Direct isinstance in condition — narrowing works."""
    if isinstance(x, int):
        # Model: assume(isfrom_int(x)) — narrowing active
        return x + 1
    return 0


def stored_isinstance_fails(x: Optional[int]) -> int:
    """Stored isinstance result — narrowing lost."""
    is_int: bool = isinstance(x, int)
    if is_int:
        # Model: NO assume(isfrom_int(x)) — narrowing NOT active
        # PAdd(x, from_int(1)) where x could be from_None → Hole
        return x + 1  # CPython: works fine; Model: Hole or error
    return 0


def negated_stored_isinstance(x: Optional[int]) -> int:
    """Negated stored result — even worse."""
    is_none: bool = not isinstance(x, int)
    if not is_none:
        # Double negation: x IS int, but model has no narrowing
        return x + 1
    return 0


def isinstance_in_variable_then_assert(x: Optional[int]) -> int:
    """Assert on stored isinstance — model can't use it."""
    is_int: bool = isinstance(x, int)
    assert is_int  # CPython: passes if x is int
    # Model: assume(is_int == True) but NO assume(isfrom_int(x))
    # The connection between is_int and x's type is LOST
    return x + 1


def isinstance_combined_with_other_condition(
    x: Optional[int], threshold: int
) -> int:
    """isinstance combined with another check in AND."""
    valid: bool = isinstance(x, int) and x > threshold
    if valid:
        # CPython: x is int AND x > threshold
        # Model: no narrowing on x; can't prove x is int
        return x - threshold
    return 0


def main() -> None:
    # Direct works
    assert direct_isinstance_works(5) == 6
    assert direct_isinstance_works(None) == 0

    # Stored fails in model but works in CPython
    assert stored_isinstance_fails(5) == 6
    assert stored_isinstance_fails(None) == 0

    # Negated stored
    assert negated_stored_isinstance(5) == 6
    assert negated_stored_isinstance(None) == 0

    # Assert on stored
    assert isinstance_in_variable_then_assert(10) == 11

    # Combined condition
    assert isinstance_combined_with_other_condition(10, 3) == 7
    assert isinstance_combined_with_other_condition(None, 3) == 0

    print("All passed")


main()
