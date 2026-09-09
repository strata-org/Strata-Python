# Dict get on just-set key — `d["x"]=5; d["x"]` needs McCarthy axiom
# `get(set(d,k,v),k)==v`; without it, read returns Hole
"""
CPython: d["x"] = 5; d["x"] → 5 (just-set key readable)
Model: DictStrAny_set prepends to assoc-list; DictStrAny_get searches
       from front. IF get finds the prepended entry, this works.
       But without the McCarthy axiom, the solver can't PROVE it.

Finding 153 identified this. This finding provides the MINIMAL program
that demonstrates the model computes INCORRECTLY (or unprovably):

CPython result: d["x"] == 5 (True, assertion passes)
Model result: DictStrAny_get(DictStrAny_set(d, "x", 5), "x") == UNKNOWN
"""


def set_then_get() -> int:
    """Set a key, immediately read it back."""
    d: dict[str, int] = {}
    d["x"] = 5
    return d["x"]  # MUST be 5


def set_two_get_first() -> int:
    """Set two keys, read the first one set."""
    d: dict[str, int] = {}
    d["a"] = 10
    d["b"] = 20
    return d["a"]  # MUST still be 10


def overwrite_then_get() -> int:
    """Overwrite a key, read it — must get new value."""
    d: dict[str, int] = {"x": 1}
    d["x"] = 99
    return d["x"]  # MUST be 99 (not 1)


def set_get_set_get() -> int:
    """Interleaved set/get operations."""
    d: dict[str, int] = {}
    d["k"] = 1
    v1: int = d["k"]  # 1
    d["k"] = 2
    v2: int = d["k"]  # 2
    return v1 + v2  # 3


def conditional_set_then_get(flag: bool) -> int:
    """Set on one branch, read after merge."""
    d: dict[str, int] = {"x": 0}
    if flag:
        d["x"] = 100
    return d["x"]  # 100 if flag, 0 otherwise


def main() -> None:
    assert set_then_get() == 5
    assert set_two_get_first() == 10
    assert overwrite_then_get() == 99
    assert set_get_set_get() == 3
    assert conditional_set_then_get(True) == 100
    assert conditional_set_then_get(False) == 0

    print(set_then_get(), overwrite_then_get(), set_get_set_get())


main()
