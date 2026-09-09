# Tuple unpack assignment `a, b = f()` — translator must decompose Tuple
# target into element extraction + individual assignments; without it,
# variables are Hole
"""
MULTIPLE RETURN VALUES VIA TUPLE UNPACKING AT CALL SITE

The subset allows:
  - Tuples (IN, though finding 028/171/218 note representation issues)
  - Function return types (IN)
  - Variable assignment (IN)

The NOVEL gap: a function returns a tuple, and the caller unpacks it
into multiple variables via `a, b = f()`. The subset document says
tuple unpacking `a, b = 1, 2` is "may grow", but the CALL-SITE
unpacking pattern `a, b = divmod(x, y)` or `a, b = f()` is distinct.

The critical issue: even if tuples have a ClassInstance encoding
(finding 218 proposes _0, _1 fields), the UNPACKING ASSIGNMENT
`a, b = expr` requires the translator to:
1. Evaluate expr to a tuple value
2. Extract element 0 → assign to a
3. Extract element 1 → assign to b

If the translator doesn't handle tuple unpacking, the assignment
either fails silently or assigns the entire tuple to `a` and leaves
`b` unbound.

  def divmod_manual(n: int, d: int) -> tuple[int, int]:
      return (n // d, n % d)

  q, r = divmod_manual(17, 5)
  # CPython: q=3, r=2
  # Model: q=ClassInstance("tuple", {"_0":3, "_1":2}), r=unbound (WRONG)
  # Or: q=Hole, r=Hole (if tuple has no representation)

This is the MOST COMMON multi-return pattern in Python. Functions like
divmod, enumerate, dict.items(), and user functions all use it.

ROOT CAUSE: Tuple unpacking assignment is a compound operation that
the translator must decompose into element extraction + individual
assignments. Without this decomposition, multi-return functions are
unusable even if tuples themselves have a representation.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def min_max(xs: list[int]) -> tuple[int, int]:
    """Return (minimum, maximum) of a non-empty list."""
    lo: int = xs[0]
    hi: int = xs[0]
    for x in xs:
        if x < lo:
            lo = x
        if x > hi:
            hi = x
    return (lo, hi)


def divmod_manual(n: int, d: int) -> tuple[int, int]:
    """Return (quotient, remainder)."""
    q: int = n // d
    r: int = n % d
    return (q, r)


def swap(a: int, b: int) -> tuple[int, int]:
    """Return swapped pair."""
    return (b, a)


def unpack_min_max() -> int:
    """Unpack tuple return into two variables, use both.
    
    CPython: lo=1, hi=9, result=8
    Model: if unpacking fails, lo and hi are wrong or unbound
    """
    xs: list[int] = [3, 1, 4, 1, 5, 9, 2, 6]
    lo: int
    hi: int
    lo, hi = min_max(xs)
    return hi - lo


def unpack_in_loop() -> int:
    """Unpack inside a loop body — each iteration produces new bindings.
    
    CPython: accumulates quotients
    Model: if unpacking fails, q is wrong each iteration
    """
    total: int = 0
    for n in [10, 20, 30, 40]:
        q: int
        r: int
        q, r = divmod_manual(n, 7)
        total += q
    return total


def unpack_and_use_both() -> bool:
    """Both unpacked values must be independently usable.
    
    CPython: a=5, b=3 → a > b is True
    Model: if a gets the whole tuple, comparison fails
    """
    a: int
    b: int
    a, b = swap(3, 5)
    return a > b


def unpack_nested_call() -> int:
    """Unpack result of function that calls another function.
    
    Tests that tuple flows correctly through call chain.
    """
    lo: int
    hi: int
    lo, hi = min_max([7, 2, 9, 4])
    q: int
    r: int
    q, r = divmod_manual(hi, lo)
    # hi=9, lo=2, q=4, r=1
    return q + r


def main() -> None:
    # Basic unpacking
    assert unpack_min_max() == 8  # 9 - 1

    # Unpacking in loop
    # 10//7=1, 20//7=2, 30//7=4, 40//7=5 → total=12
    assert unpack_in_loop() == 12

    # Both values usable
    assert unpack_and_use_both() == True  # 5 > 3

    # Nested calls with unpacking
    assert unpack_nested_call() == 5  # 4 + 1

    # Direct unpacking test
    x: int
    y: int
    x, y = swap(10, 20)
    assert x == 20
    assert y == 10

    print("all passed")


main()
