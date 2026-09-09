# Container truthiness `if xs:` — `Any_to_bool(from_ListAny)` needs `List_len
# > 0` check; requires axioms from finding 088
"""
Container truthiness in conditions — `if xs:` needs length-based dispatch.

In CPython, empty containers are falsy, non-empty are truthy:
  bool([])      → False
  bool([1,2])   → True
  bool({})      → False
  bool({"a":1}) → True

When used in conditions: `if xs:` is equivalent to `if len(xs) > 0:`.

Finding 016 covers ClassInstance truthiness (always True, returns Hole).
Finding 059 covers non-bool conditions generally.
Finding 139 covers bool() conversion dispatch.

This finding specifically tests that `Any_to_bool(from_ListAny(lst))`
and `Any_to_bool(from_DictStrAny(d))` must check container LENGTH,
which requires List_len/DictStrAny_len to be defined AND connected
to the truthiness function. Since List_len has no axioms (finding 088),
even if the dispatch exists, the result may be unprovable.

Uses ONLY confirmed-accepted constructs: list, dict, if, bool, len.
"""


def list_truthy_nonempty(xs: list[int]) -> str:
    """Non-empty list is truthy."""
    if xs:
        return "has elements"
    return "empty"
    # CPython with xs=[1,2,3]: "has elements"
    # Model: Any_to_bool(from_ListAny(cons(...))) → ?
    #   If Hole: non-deterministic branch
    #   If always True: wrong for empty list
    #   If needs List_len > 0: requires axioms


def list_truthy_empty() -> str:
    """Empty list is falsy."""
    xs: list[int] = []
    if xs:
        return "has elements"
    return "empty"
    # CPython: "empty" ([] is falsy)
    # Model: if Any_to_bool returns Hole, may take either branch


def dict_truthy_nonempty(d: dict[str, int]) -> bool:
    """Non-empty dict is truthy."""
    if d:
        return True
    return False
    # CPython with d={"a":1}: True
    # Model: Any_to_bool(from_DictStrAny(entry(...))) → ?


def dict_truthy_empty() -> bool:
    """Empty dict is falsy."""
    d: dict[str, int] = {}
    if d:
        return True
    return False
    # CPython: False ({} is falsy)


def guard_before_access(xs: list[int]) -> int:
    """Common pattern: check truthiness before accessing."""
    if xs:
        return xs[0]  # safe because xs is non-empty
    return -1
    # CPython: works correctly
    # Model: even if branch is taken, can't prove len(xs) > 0
    #   because truthiness → length connection is missing


def while_container_drain(xs: list[int]) -> int:
    """While loop using container truthiness as condition."""
    total: int = 0
    remaining: list[int] = xs
    # Note: this pattern requires list operations we may not have
    # but the truthiness check itself is the issue
    if remaining:
        total = total + remaining[0]
    return total


def main() -> None:
    assert list_truthy_nonempty([1, 2, 3]) == "has elements"
    assert list_truthy_empty() == "empty"
    assert dict_truthy_nonempty({"a": 1}) == True
    assert dict_truthy_empty() == False
    assert guard_before_access([10, 20]) == 10
    assert guard_before_access([]) == -1
