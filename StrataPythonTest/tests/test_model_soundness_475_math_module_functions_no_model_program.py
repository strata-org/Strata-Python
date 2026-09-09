# `math` module functions (sqrt, floor, ceil) are IN but have no Laurel model
# — return Hole; trivial SMT-LIB Real mappings available
"""
MATH MODULE FUNCTIONS HAVE NO LAUREL MODEL

The subset allows:
  - `import math` (IN)
  - `math.sqrt(x)`, `math.floor(x)`, `math.ceil(x)` (IN — stdlib allowlist)
  - Float arithmetic (IN)
  - Comparison operators on floats (IN)

The NOVEL gap: math module functions are IN the subset but have no
Laurel model. Unlike string methods (finding 019/220) which return Hole,
math functions have well-defined mathematical semantics that MAP DIRECTLY
to SMT-LIB theories (Real arithmetic, rounding).

Key differences from string method findings:
  - math.sqrt has a PRECISE mathematical definition: sqrt(x) * sqrt(x) == x
  - math.floor/ceil have PRECISE definitions: floor(x) <= x < floor(x)+1
  - These map to SMT-LIB `(^ x 0.5)`, `(to_int x)`, `(+ (to_int x) 1)`
  - The model uses SMT Real (finding 042), so math functions are EXACT

CPython behavior:
  - math.sqrt(4.0) → 2.0
  - math.floor(3.7) → 3 (returns int!)
  - math.ceil(3.2) → 4 (returns int!)
  - math.sqrt(-1.0) → raises ValueError

Model behavior:
  - All math.* calls return Hole (uninterpreted function, no axioms)
  - Properties like sqrt(x) >= 0 for x >= 0 are unprovable
  - Return TYPE is wrong: floor/ceil return int, model doesn't know this

DISTINCT FROM:
  - Finding 019/220 (string methods no model) — math functions have
    exact SMT-LIB equivalents; string methods need theory solvers
  - Finding 026 (min/max/abs no model) — those are builtins; math.*
    are module functions with different dispatch
  - Finding 080 (float division by zero) — math.sqrt(-1) is a different
    error condition (domain error, not division)
"""
import math


def hypotenuse(a: float, b: float) -> float:
    """Pythagorean theorem using math.sqrt."""
    return math.sqrt(a * a + b * b)


def safe_sqrt(x: float) -> float:
    """Guard against negative input."""
    if x < 0.0:
        return 0.0
    result: float = math.sqrt(x)
    # CPython: result >= 0.0 (always true for non-negative input)
    # Model: result is Hole; `result >= 0.0` is Unknown
    return result


def round_down(x: float) -> int:
    """math.floor returns int, not float."""
    n: int = math.floor(x)
    # CPython: n is an int (e.g., floor(3.7) == 3)
    # Model: n is Hole; subsequent int operations on n produce Hole
    return n


def round_up(x: float) -> int:
    """math.ceil returns int, not float."""
    n: int = math.ceil(x)
    return n


def floor_ceil_relationship(x: float) -> bool:
    """floor(x) <= ceil(x) is always true."""
    f: int = math.floor(x)
    c: int = math.ceil(x)
    # CPython: always True (mathematical fact)
    # Model: f and c are both Hole; comparison is Hole; unprovable
    return f <= c


def sqrt_of_square(x: float) -> float:
    """sqrt(x*x) == abs(x) for all x."""
    if x < 0.0:
        x = -x
    result: float = math.sqrt(x * x)
    # CPython: result == x (for non-negative x, exact in reals)
    # Model: result is Hole; equality with x is Unknown
    return result


def main() -> None:
    h: float = hypotenuse(3.0, 4.0)
    assert h == 5.0, f"Expected 5.0, got {h}"

    s: float = safe_sqrt(9.0)
    assert s == 3.0, f"Expected 3.0, got {s}"
    assert safe_sqrt(-1.0) == 0.0

    f: int = round_down(3.7)
    assert f == 3, f"Expected 3, got {f}"

    c: int = round_up(3.2)
    assert c == 4, f"Expected 4, got {c}"

    assert floor_ceil_relationship(2.5)
    assert floor_ceil_relationship(-1.3)

    print(h, s, f, c)


main()
