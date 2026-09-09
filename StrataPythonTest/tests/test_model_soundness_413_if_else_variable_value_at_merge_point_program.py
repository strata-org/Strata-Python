# If/else variable merge — `if c: x=1 else: x=2` must produce `ite(c,1,2)` at
# join; wrong merge gives always-one-branch value
"""
IF/ELSE VARIABLE VALUE AT MERGE POINT — BOTH BRANCHES MUST CONTRIBUTE

CPython: if cond: x = 1 else: x = 2
         After if/else: x is EITHER 1 OR 2 (depending on cond)
         x >= 1 and x <= 2 → True (always)

Model:   The translator must produce:
         x = ite(cond, 1, 2)  — or equivalent SSA merge

         If the translator only keeps the LAST assignment:
         x = 2 (else branch always wins) → WRONG for cond=True

         If the translator only keeps the FIRST assignment:
         x = 1 (if branch always wins) → WRONG for cond=False

CPython result: x depends on cond
Model result (if broken): x is always one branch's value

Root cause: Missing phi-node / ite at the merge point after if/else.
Finding 255 identified this conceptually. This provides the concrete test.
"""


def abs_value(n: int) -> int:
    """Classic if/else: result depends on condition."""
    if n >= 0:
        result: int = n
    else:
        result = -n
    # After merge: result >= 0 (both branches produce non-negative)
    return result


def max_of_two(a: int, b: int) -> int:
    """If/else assigns to same variable in both branches."""
    if a >= b:
        m: int = a
    else:
        m = b
    return m


def classify(n: int) -> str:
    """Multi-branch: each assigns to same variable."""
    if n > 0:
        label: str = "positive"
    elif n < 0:
        label = "negative"
    else:
        label = "zero"
    return label


def conditional_computation(x: int, flag: bool) -> int:
    """Different computations in each branch."""
    if flag:
        result: int = x * 2
    else:
        result = x + 10
    # result is either x*2 or x+10
    return result


def main() -> None:
    # Test 1: abs
    assert abs_value(5) == 5
    assert abs_value(-3) == 3
    assert abs_value(0) == 0

    # Test 2: max
    assert max_of_two(7, 3) == 7
    assert max_of_two(3, 7) == 7
    assert max_of_two(5, 5) == 5

    # Test 3: classify
    assert classify(5) == "positive"
    assert classify(-3) == "negative"
    assert classify(0) == "zero"

    # Test 4: conditional computation
    assert conditional_computation(5, True) == 10
    assert conditional_computation(5, False) == 15

    print("all passed")


main()
