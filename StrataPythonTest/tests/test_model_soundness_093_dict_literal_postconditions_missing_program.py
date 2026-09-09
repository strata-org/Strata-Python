# Dict literal has no postconditions — solver can't prove `d["a"] == 1` after
# `d = {"a": 1}`; needs McCarthy read-over-write axioms
"""
A dict literal `{"a": 1, "b": 2}` must produce a DictStrAny where:
- DictStrAny_contains(d, "a") == True
- DictStrAny_get(d, "a") == from_int(1)
- DictStrAny_contains(d, "b") == True
- DictStrAny_get(d, "b") == from_int(2)
- DictStrAny_len(d) == 2
- DictStrAny_contains(d, "c") == False

Without postconditions establishing these facts, the solver cannot
prove anything about dict contents after construction.
"""


def lookup_literal() -> int:
    d: dict[str, int] = {"x": 10, "y": 20, "z": 30}
    return d["x"] + d["y"] + d["z"]


def contains_check() -> bool:
    d: dict[str, int] = {"a": 1, "b": 2}
    return "a" in d and "b" in d and "c" not in d


def literal_len() -> int:
    d: dict[str, int] = {"one": 1, "two": 2, "three": 3}
    return len(d)


def overwrite_in_literal() -> int:
    # Duplicate key in literal: last value wins
    d: dict[str, int] = {"x": 1, "x": 2}  # type: ignore
    return d["x"]


def empty_dict_properties() -> bool:
    d: dict[str, int] = {}
    return len(d) == 0 and "a" not in d


def main() -> None:
    # Lookup from literal
    assert lookup_literal() == 60

    # Contains on literal keys
    assert contains_check() == True

    # Length of literal
    assert literal_len() == 3

    # Duplicate key: last wins
    assert overwrite_in_literal() == 2

    # Empty dict
    assert empty_dict_properties() == True

    print(lookup_literal(), contains_check(), literal_len())


main()
