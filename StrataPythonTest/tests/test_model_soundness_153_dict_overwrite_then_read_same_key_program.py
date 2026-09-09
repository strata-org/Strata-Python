# Dict overwrite then read same key — `d["x"]=3; d["x"]` must return 3;
# requires McCarthy `get(set(d,k,v),k)==v` axiom
"""
Overwrite a dict key then read it back. The model's DictStrAny_set
prepends a new entry; DictStrAny_get must find the MOST RECENT entry.
Without McCarthy axioms, `d["x"]` after `d["x"] = 5` is unprovable.

Uses ONLY frontend-confirmed constructs: dict create, dict assign,
dict subscript, if, while, function def with annotations.
"""


def overwrite_and_read() -> int:
    d: dict[str, int] = {}
    d["x"] = 1
    d["x"] = 2
    d["x"] = 3
    # Must read the LAST written value
    return d["x"]


def conditional_write(flag: bool) -> int:
    d: dict[str, int] = {}
    d["key"] = 0
    if flag:
        d["key"] = 100
    # If flag: d["key"] == 100. Else: d["key"] == 0.
    return d["key"]


def write_read_different_keys() -> int:
    d: dict[str, int] = {}
    d["a"] = 10
    d["b"] = 20
    d["c"] = 30
    # Reading "a" must still return 10 (not affected by "b"/"c" writes)
    return d["a"] + d["b"] + d["c"]


def loop_write_read(n: int) -> int:
    d: dict[str, int] = {}
    i: int = 0
    while i < n:
        d["counter"] = i
        i = i + 1
    # After loop: d["counter"] == n-1
    return d["counter"]


def main() -> None:
    # Overwrite: last write wins
    assert overwrite_and_read() == 3

    # Conditional write
    assert conditional_write(True) == 100
    assert conditional_write(False) == 0

    # Different keys are independent
    assert write_read_different_keys() == 60

    # Loop write
    assert loop_write_read(5) == 4

    print(overwrite_and_read(), conditional_write(True), write_read_different_keys())


main()
