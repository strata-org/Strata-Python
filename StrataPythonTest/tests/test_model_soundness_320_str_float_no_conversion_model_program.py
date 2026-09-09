# `str(float)` has no conversion model — `str(3.14)` produces Hole; no float-
# to-string axioms or formatting
"""
str(float) has no conversion model — float-to-string formatting undefined.

In CPython, `str(3.14)` produces `"3.14"`, `str(0.1)` produces `"0.1"`,
and `str(1e10)` produces `"10000000000.0"`. The formatting follows
Python's float repr algorithm (shortest representation that round-trips).

The Laurel model's `to_str_any` (or `Any_to_str`) for `from_float` has
no definition. Like finding 053 (str↔int roundtrip), the float-to-string
conversion is uninterpreted, producing Hole.

This means:
- `str(3.14)` → Hole (unconstrained string)
- `f"{x}"` where x is float → Hole (via finding 083/227)
- `str(x) == "3.14"` → unprovable (Hole == "3.14" is unknown)
- `float(str(x)) == x` → unprovable (no roundtrip axiom)

Additionally, the model uses exact Real (finding 174), so even if
str(float) were defined, the formatting would differ:
- Model: str(from_float(1/10)) might produce "0.1" (exact)
- CPython: str(0.1) produces "0.1" (shortest repr of 0.1000...00001)
- These happen to agree, but str(from_float(1/3)) would be "0.333..."
  while CPython gives "0.3333333333333333"

Uses ONLY confirmed-accepted constructs: str(), float, int, comparison.
"""


def float_to_str_basic() -> str:
    """str(float) must produce a string representation."""
    x: float = 3.14
    result: str = str(x)
    # CPython: "3.14"
    # Model: Hole (no to_str for from_float)
    return result


def float_to_str_integer_value() -> str:
    """str(float) on integer-valued float includes decimal point."""
    x: float = 5.0
    result: str = str(x)
    # CPython: "5.0" (NOT "5" — it's a float)
    # Model: Hole
    return result


def float_to_str_negative() -> str:
    """str(negative float) includes minus sign."""
    x: float = -2.5
    result: str = str(x)
    # CPython: "-2.5"
    # Model: Hole
    return result


def float_str_comparison() -> bool:
    """Using str(float) in comparison — unprovable."""
    x: float = 3.14
    s: str = str(x)
    # CPython: s == "3.14" → True
    # Model: s is Hole, comparison is unknown
    return s == "3.14"


def float_str_in_message(value: float, limit: float) -> str:
    """Common pattern: building error/log messages with float values."""
    if value > limit:
        return "exceeded: " + str(value)
    return "ok: " + str(value)
    # CPython with value=3.14, limit=2.0: "exceeded: 3.14"
    # Model: "exceeded: " + Hole = Hole (string concat with Hole)


def int_to_float_to_str() -> str:
    """Chain: int → float → str."""
    n: int = 42
    f: float = float(n)  # finding 140: float() may be Hole
    s: str = str(f)
    # CPython: "42.0"
    # Model: Hole (both conversions undefined)
    return s


def main() -> None:
    assert float_to_str_basic() == "3.14"
    assert float_to_str_integer_value() == "5.0"
    assert float_to_str_negative() == "-2.5"
    assert float_str_comparison() == True
    assert float_str_in_message(3.14, 2.0) == "exceeded: 3.14"
    assert int_to_float_to_str() == "42.0"
