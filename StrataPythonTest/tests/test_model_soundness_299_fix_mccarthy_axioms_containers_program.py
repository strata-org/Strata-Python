# **FIX: McCarthy axioms (or SMT Array/String theory)** — get(set(c,k,v),k)==v
# + len axioms; resolves 14+ findings
"""
FIX PROPOSAL: McCarthy read-over-write axioms for containers.
Resolves findings: 078, 081, 088, 089, 093, 141, 151, 153, 183,
232, 233, 252, 253, 254.

The fix: add axioms connecting get/set/len for both lists and dicts.
Or better: use SMT-LIB Array theory which provides these natively.
"""


def list_write_read() -> bool:
    """After write, read same index returns written value."""
    xs: list[int] = [10, 20, 30]
    xs[1] = 99
    return xs[1] == 99  # McCarthy: get(set(xs, 1, 99), 1) == 99


def list_write_preserves_other() -> bool:
    """After write, other indices unchanged."""
    xs: list[int] = [10, 20, 30]
    xs[1] = 99
    return xs[0] == 10 and xs[2] == 30  # get(set(xs,1,99), 0) == get(xs,0)


def dict_write_read() -> bool:
    """After set, get same key returns set value."""
    d: dict[str, int] = {}
    d["x"] = 42
    return d["x"] == 42  # get(set(d, "x", 42), "x") == 42


def dict_write_preserves_other() -> bool:
    """After set, other keys unchanged."""
    d: dict[str, int] = {"a": 1, "b": 2}
    d["a"] = 99
    return d["b"] == 2  # get(set(d, "a", 99), "b") == get(d, "b")


def literal_postconditions() -> bool:
    """Literal construction establishes known values."""
    xs: list[int] = [10, 20, 30]
    return xs[0] == 10 and xs[1] == 20 and len(xs) == 3


def string_concat_length() -> bool:
    """len(a + b) == len(a) + len(b)."""
    a: str = "hello"
    b: str = " world"
    return len(a + b) == len(a) + len(b)


def main() -> None:
    assert list_write_read() == True
    assert list_write_preserves_other() == True
    assert dict_write_read() == True
    assert dict_write_preserves_other() == True
    assert literal_postconditions() == True
    assert string_concat_length() == True

    print("All McCarthy axiom tests pass")


main()
