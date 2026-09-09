# `return` may not terminate control flow — if translated as assignment
# without goto/assume-false, subsequent code executes
"""
When a function has multiple return statements on different branches,
each returns a value. In CPython, exactly one return executes. In the
Laurel model, if `return` is translated as assigning to a result variable
without immediately terminating the function, subsequent statements
(including other returns) may execute, overwriting the correct result.

This is the dual of finding 014 (raise silently dropped): if `return`
doesn't terminate control flow in the model, code after it is reachable.
"""


def classify(n: int) -> str:
    if n > 0:
        return "positive"
    if n < 0:
        return "negative"
    return "zero"


def first_positive(xs: list[int]) -> int:
    for x in xs:
        if x > 0:
            return x
    return -1


def early_exit(n: int) -> int:
    if n == 0:
        return 42
    # CPython: unreachable when n == 0
    # Model: if return doesn't terminate, this executes
    result: int = n * 2
    if result > 100:
        return 100
    return result


def main() -> None:
    # classify: only one branch executes
    assert classify(5) == "positive"
    assert classify(-3) == "negative"
    assert classify(0) == "zero"

    # first_positive: early return from loop
    assert first_positive([0, -1, 3, 5]) == 3
    assert first_positive([-1, -2]) == -1

    # early_exit: return terminates, skips rest
    assert early_exit(0) == 42
    assert early_exit(10) == 20
    assert early_exit(60) == 100

    print(classify(5), first_positive([0, -1, 3, 5]), early_exit(0))


main()
