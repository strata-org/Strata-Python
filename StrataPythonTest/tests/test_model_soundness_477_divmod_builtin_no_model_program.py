# Floor-div and modulo joint invariant `a == (a//b)*b + (a%b)` not axiomatized
# — operations computed independently; reconstruction/bounds unprovable
"""
DIVMOD BUILTIN HAS NO MODEL — RETURNS TUPLE, USED IN SUBSET PATTERNS

The subset allows:
  - Builtin functions (IN): len, range, min, max, abs, sum
  - Integer arithmetic (IN): //, %
  - Tuple types (IN, though representation is problematic — finding 218)

The NOVEL gap: while `divmod` is not explicitly listed in the IN builtins,
the pattern `q, r = divmod(a, b)` is equivalent to `q = a // b; r = a % b`
which IS fully IN. The issue is that even the MANUAL equivalent has a
compound problem:

  1. `//` and `%` must be computed CONSISTENTLY (same quotient/remainder pair)
  2. The invariant `a == q * b + r` must hold
  3. If translated independently, the solver treats them as unrelated

More importantly, this finding demonstrates that EVEN WITHOUT divmod,
the relationship between `//` and `%` is not axiomatized:

    q = a // b
    r = a % b
    assert a == q * b + r  # UNPROVABLE in model

CPython guarantees this invariant (it's the definition of floor division).
The model computes `//` and `%` independently with no connecting axiom.

DISTINCT FROM:
  - Finding 273 (SMT div ≠ Python //) — that's about WRONG VALUES;
    this is about the RELATIONSHIP between // and % being unaxiomatized
  - Finding 297 (fix floor-div/mod) — that fixes individual operations;
    this is about the JOINT invariant connecting them
  - Finding 028/218 (tuple no representation) — that's about the return
    type; this is about the arithmetic invariant
"""


def manual_divmod(a: int, b: int) -> int:
    """The divmod invariant: a == (a//b)*b + (a%b)."""
    q: int = a // b
    r: int = a % b
    # CPython: a == q * b + r is ALWAYS true (definition of floor div)
    # Model: q and r are computed independently; no connecting axiom
    # Even if // and % are individually correct, solver can't prove
    # the relationship without an explicit axiom
    check: int = q * b + r
    return check  # Should always equal a


def euclidean_algorithm(a: int, b: int) -> int:
    """GCD using the divmod relationship."""
    while b > 0:
        r: int = a % b
        # Invariant: 0 <= r < b (definition of Python %)
        # Model: r is some int; can't prove 0 <= r < b
        a = b
        b = r
    return a


def is_divisible(a: int, b: int) -> bool:
    """Check if a is divisible by b using %."""
    r: int = a % b
    # CPython: r == 0 iff b divides a
    # Model: can prove r == 0 only if % has correct axioms AND
    #   the solver knows a % b == 0 ⟺ exists k. a == k * b
    return r == 0


def quotient_remainder_bounds(a: int, b: int) -> bool:
    """Remainder is always in [0, b) for positive b."""
    if b <= 0:
        return True
    r: int = a % b
    # CPython: 0 <= r < b (always, for positive b)
    # Model: r is unconstrained int; can't prove bounds
    return r >= 0 and r < b


def division_reconstruction(a: int, b: int) -> bool:
    """Reconstruct a from quotient and remainder."""
    if b == 0:
        return True
    q: int = a // b
    r: int = a % b
    # The FUNDAMENTAL invariant of integer division:
    # a == q * b + r AND 0 <= r < abs(b)
    # CPython: always holds
    # Model: q and r are independent symbolic values; unprovable
    reconstructed: int = q * b + r
    return reconstructed == a


def main() -> None:
    # divmod invariant
    assert manual_divmod(17, 5) == 17
    assert manual_divmod(-7, 3) == -7
    assert manual_divmod(100, 7) == 100

    # GCD
    assert euclidean_algorithm(48, 18) == 6
    assert euclidean_algorithm(100, 25) == 25

    # Divisibility
    assert is_divisible(15, 5)
    assert not is_divisible(17, 5)

    # Bounds
    assert quotient_remainder_bounds(17, 5)
    assert quotient_remainder_bounds(-7, 3)

    # Reconstruction
    assert division_reconstruction(17, 5)
    assert division_reconstruction(-7, 3)
    assert division_reconstruction(0, 5)

    print("All passed")


main()
