# `k in d` after `d[k] = v` unprovable — no axiom connecting DictStrAny_set to
# DictStrAny_contains; guard patterns broken
"""
`k in d` AFTER `d[k] = v` — NO AXIOM CONNECTING SET TO CONTAINS

CPython: d = {}; d["x"] = 1; "x" in d → True (always)

Model:   d' = DictStrAny_set(empty, "x", 1)
         DictStrAny_contains(d', "x") == ???

         There is no axiom:
           DictStrAny_contains(DictStrAny_set(d, k, v), k) == True

         Without it, the solver cannot prove that a key EXISTS after
         being set. This breaks the common pattern:
           d[k] = v
           if k in d:  # should always be True after set!
               use(d[k])
"""


def set_then_check() -> bool:
    """After setting a key, `in` must return True."""
    d: dict[str, int] = {}
    d["x"] = 42
    # CPython: "x" in d → True (just set it!)
    # Model: DictStrAny_contains(d', "x") → unconstrained
    return "x" in d


def set_then_check_other() -> bool:
    """After setting key k, checking different key k2."""
    d: dict[str, int] = {"y": 10}
    d["x"] = 42
    # "y" should still be in d (frame axiom for contains)
    # "x" should now be in d (set-contains axiom)
    return "x" in d and "y" in d


def guard_pattern(d: dict[str, int], key: str, value: int) -> int:
    """Common pattern: set then guard before access."""
    d[key] = value
    if key in d:
        return d[key]
    return -1  # should be unreachable after set


def build_and_check_membership() -> bool:
    """Build dict, verify all keys present."""
    d: dict[str, int] = {}
    d["a"] = 1
    d["b"] = 2
    d["c"] = 3
    # All three keys must be `in d`
    return "a" in d and "b" in d and "c" in d


def contains_after_overwrite() -> bool:
    """Overwriting a key — still in dict."""
    d: dict[str, int] = {"x": 1}
    d["x"] = 99  # overwrite
    return "x" in d  # still True


def main() -> None:
    assert set_then_check()
    assert set_then_check_other()
    assert guard_pattern({}, "key", 100) == 100
    assert build_and_check_membership()
    assert contains_after_overwrite()

    print("all passed")


main()
