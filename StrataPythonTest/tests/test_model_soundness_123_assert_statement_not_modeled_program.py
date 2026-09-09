# `assert` statement — must translate as Laurel assert (check + assume); if
# dropped, verifier loses invariant info
"""
Python's `assert expr` raises AssertionError if expr is falsy. In the
model, `assert` could be translated as:
1. A Laurel `assert` (verification condition — correct)
2. Dropped entirely (code after assert is reachable even when expr is False)
3. An if-then-raise (exception-as-value, with all its issues)

The key question: does `assert x > 0` in the SOURCE translate to an
assertion the VERIFIER checks, or is it modeled as runtime behavior?
"""


def positive_only(x: int) -> int:
    assert x > 0
    # After assert: x > 0 is known to be true
    # The verifier should be able to prove x > 0 here
    return x - 1  # safe: x >= 1, so x - 1 >= 0


def bounded(x: int, lo: int, hi: int) -> int:
    assert lo <= x <= hi
    # After assert: lo <= x <= hi is known
    return x - lo  # safe: >= 0


def non_empty_list(lst: list[int]) -> int:
    assert len(lst) > 0
    # After assert: list is non-empty, so lst[0] is safe
    return lst[0]


def assert_as_precondition(n: int) -> int:
    """Assert acts as a precondition — code after it can assume the condition."""
    assert n != 0
    return 100 // n  # safe: n != 0


def main() -> None:
    # Assert passes: normal execution
    assert positive_only(5) == 4
    assert bounded(5, 0, 10) == 5
    assert non_empty_list([1, 2, 3]) == 1
    assert assert_as_precondition(5) == 20

    # Assert fails: raises AssertionError
    raised: bool = False
    try:
        positive_only(-1)
    except AssertionError:
        raised = True
    assert raised == True

    print(positive_only(5), bounded(5, 0, 10), raised)


main()
