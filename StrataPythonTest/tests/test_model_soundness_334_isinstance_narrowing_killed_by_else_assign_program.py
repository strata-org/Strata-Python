# isinstance narrowing killed at branch merge — narrowing from if-branch must
# not leak past else-branch assignment
"""
isinstance narrowing killed by assignment in else branch.

Finding 162 covers narrowing invalidated by reassignment. This finding
tests a subtler case: narrowing in the if-branch must NOT persist into
the else-branch, and vice versa.

    x: Optional[int] = get_value()
    if isinstance(x, int):
        # Here: x is int (narrowed)
        use_int(x)
    else:
        # Here: x is None (narrowed to complement)
        x = 42  # reassignment
    # Here: x could be int from either branch
    # The narrowing from the if-branch must NOT leak here

The model must:
1. Narrow x to int in the if-branch
2. Narrow x to None in the else-branch
3. At the merge point: x has the UNION of both branch outcomes

If the model keeps the if-branch narrowing active after the merge,
it incorrectly assumes x is always int — missing the case where
the else-branch assigned a different value.

Uses ONLY confirmed-accepted constructs: isinstance, if/else, Optional, int.
"""


def narrow_and_merge(x: object) -> int:
    """After if/else, narrowing from one branch must not persist."""
    if isinstance(x, int):
        result: int = x + 1
    else:
        result = 0
    # At this point, result is int from either branch
    # But x's narrowing (int vs not-int) must not leak
    return result


def narrow_else_assigns(x: object) -> int:
    """Else branch assigns — narrowing from if must be killed at merge."""
    val: int = 0
    if isinstance(x, int):
        val = x * 2  # x narrowed to int here
    else:
        val = -1
    # After merge: val is int (from either branch)
    # x's type at this point is UNKNOWN (could be either branch)
    return val


def narrow_both_branches(x: object) -> str:
    """Both branches narrow differently."""
    if isinstance(x, int):
        # x is int
        return "int: " + str(x)
    elif isinstance(x, str):
        # x is str
        return "str: " + x
    else:
        return "other"


def narrow_then_reassign_in_branch(x: object) -> int:
    """Reassignment inside narrowed branch kills narrowing."""
    if isinstance(x, int):
        y: int = x  # x is int here
        x = "hello"  # type: ignore  # reassign x — narrowing killed
        # x is now str, NOT int
        # Model must not assume x is still int
        return y
    return 0


def main() -> None:
    assert narrow_and_merge(5) == 6
    assert narrow_and_merge("hello") == 0
    assert narrow_else_assigns(5) == 10
    assert narrow_else_assigns("hello") == -1
    assert narrow_both_branches(42) == "int: 42"
    assert narrow_both_branches("hi") == "str: hi"
    assert narrow_both_branches(3.14) == "other"
    assert narrow_then_reassign_in_branch(5) == 5
