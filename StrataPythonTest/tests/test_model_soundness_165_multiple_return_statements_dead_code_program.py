# Multiple return statements — code after `return` must be unreachable;
# without `assume(false)`, last return always wins
"""
When a function has multiple return statements, code after an earlier
return is DEAD (unreachable). The model must ensure that once a return
is hit, no subsequent statements execute.

This interacts with finding 052 (return doesn't terminate control flow)
but focuses on a specific pattern: multiple returns with DIFFERENT values
where the model might execute all of them and return the LAST one.

If `return` is translated as `result := value` without termination,
then:
    def f(x: int) -> int:
        if x > 0:
            return 1    # result := 1
        return -1       # result := -1  ← ALWAYS executes, overwriting!

The function would always return -1 regardless of x.

Uses ONLY confirmed-accepted constructs: if/else, return, int, function def.
"""


def sign(x: int) -> int:
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0


def early_return_guard(x: int) -> int:
    if x < 0:
        return 0  # guard: reject negative
    # Only reached if x >= 0
    return x * x


def cascading_returns(x: int) -> int:
    if x > 100:
        return 3
    if x > 10:
        return 2
    if x > 0:
        return 1
    return 0


def return_in_loop(xs: list[int], target: int) -> int:
    for x in xs:
        if x == target:
            return x  # early exit from loop
    return -1  # not found


def return_after_return_dead(x: int) -> int:
    """The second return is dead code — never reached."""
    if x > 0:
        return x
    else:
        return -x
    # This line is unreachable in CPython
    # If model executes it, result is wrong
    return 999


def main() -> None:
    # sign function
    assert sign(5) == 1
    assert sign(-3) == -1
    assert sign(0) == 0

    # early return guard
    assert early_return_guard(-5) == 0
    assert early_return_guard(3) == 9
    assert early_return_guard(0) == 0

    # cascading
    assert cascading_returns(200) == 3
    assert cascading_returns(50) == 2
    assert cascading_returns(5) == 1
    assert cascading_returns(-1) == 0

    # return in loop
    assert return_in_loop([1, 2, 3, 4, 5], 3) == 3
    assert return_in_loop([1, 2, 3], 9) == -1

    # dead code after exhaustive if/else
    assert return_after_return_dead(7) == 7
    assert return_after_return_dead(-4) == 4

    print(sign(5), early_return_guard(3), cascading_returns(50))


main()
