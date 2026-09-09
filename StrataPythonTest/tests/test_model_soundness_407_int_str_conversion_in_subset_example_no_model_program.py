# `int(s)`/`str(n)` conversions have no model — subset examples use them;
# roundtrip `int(str(n))==n` unprovable; map to SMT-LIB str.to_int
"""
int()/str() CONVERSION IN SUBSET EXAMPLE — NO MODEL

The subset's parse_positive example uses int(s):
    n: int = int(s)

CPython: int("42") → 42, int("abc") → ValueError
Model:   int(s) → Hole (uninterpreted, finding 017)

Similarly str(n) is used in f-strings and logging:
    msg = "value: " + str(n)

CPython: str(42) → "42"
Model:   str(n) → Hole (no int-to-str model, finding 053)

These are the TWO MOST BASIC type conversions in Python.
Without them, the subset's own examples don't work.
"""


def int_from_str(s: str) -> int:
    """Basic int conversion — the subset's core use case."""
    return int(s)


def str_from_int(n: int) -> str:
    """Basic str conversion — needed for f-strings and logging."""
    return str(n)


def roundtrip(n: int) -> bool:
    """int(str(n)) == n — the fundamental conversion axiom."""
    return int(str(n)) == n


def parse_and_compute(s: str) -> int:
    """Parse then arithmetic — needs int() to return from_int."""
    n: int = int(s)
    return n * 2 + 1


def format_result(value: int, label: str) -> str:
    """Format with str() — needs str() to return from_str."""
    return label + ": " + str(value)


def main() -> None:
    # Test 1: int from string
    assert int_from_str("42") == 42
    assert int_from_str("0") == 0
    assert int_from_str("-7") == -7

    # Test 2: str from int
    assert str_from_int(42) == "42"
    assert str_from_int(0) == "0"
    assert str_from_int(-7) == "-7"

    # Test 3: roundtrip
    assert roundtrip(42)
    assert roundtrip(0)
    assert roundtrip(-100)

    # Test 4: parse then compute
    assert parse_and_compute("5") == 11  # 5*2+1

    # Test 5: format
    assert format_result(42, "answer") == "answer: 42"

    print("all passed")


main()
