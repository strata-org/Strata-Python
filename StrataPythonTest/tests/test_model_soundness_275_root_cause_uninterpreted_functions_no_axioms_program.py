# **ROOT CAUSE: Uninterpreted functions no axioms** —
# List_get/DictStrAny_get/str_concat are opaque; 35+ findings unprovable
"""
ROOT CAUSE: Operations like List_get, DictStrAny_get, str_concat,
string_repeat, str_len are UNINTERPRETED FUNCTIONS with no axioms.

PROPERTY: The solver treats them as opaque — can't evaluate concrete
cases or derive relationships between operations.

This causes findings:
015, 019, 020, 021, 026, 046, 047, 053, 060, 068, 069, 071, 075,
081, 083, 088, 089, 091, 093, 133, 134, 135, 138, 141, 144, 151,
152, 153, 167, 183, 220, 232, 252, 253, 254.

DEMONSTRATION: Write then read returns unknown; concat length unknown.
"""


def write_read_list() -> int:
    """List_get(List_set(xs, 0, 99), 0) should be 99 but is unknown."""
    xs: list[int] = [1, 2, 3]
    xs[0] = 99
    return xs[0]  # Model: unknown (no McCarthy axiom)


def write_read_dict() -> int:
    """DictStrAny_get(DictStrAny_set(d, "k", 5), "k") should be 5."""
    d: dict[str, int] = {}
    d["k"] = 5
    return d["k"]  # Model: unknown (no McCarthy axiom)


def concat_length() -> int:
    """len("ab" + "cd") should be 4 but is unknown."""
    s: str = "ab" + "cd"
    return len(s)  # Model: unknown (str_len(str_concat(...)) has no axiom)


def literal_access() -> int:
    """[10, 20, 30][1] should be 20 but is unknown."""
    xs: list[int] = [10, 20, 30]
    return xs[1]  # Model: unknown (no literal postcondition)


def empty_list_length() -> int:
    """len([]) should be 0 but is unknown."""
    return len([])  # Model: unknown (no base-case axiom)


def main() -> None:
    assert write_read_list() == 99
    assert write_read_dict() == 5
    assert concat_length() == 4
    assert literal_access() == 20
    assert empty_list_length() == 0

    print(write_read_list(), write_read_dict(), concat_length())


main()
