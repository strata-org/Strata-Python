# Assert as assume loses error path — `assert x>0` with x=-5 should report
# error; assume-only prunes the path silently
"""
ASSERT AS ASSUME — LOSES THE ERROR PATH

CPython: assert x > 0 → if x <= 0: raises AssertionError
         Code AFTER assert can rely on x > 0.
         Code that CATCHES AssertionError can handle the failure.

Model:   If assert translates to ONLY `assume(x > 0)`:
         - Post-assert code correctly knows x > 0 ✓
         - BUT: the failure path (x <= 0) is INVISIBLE
         - Programs where assert FAILS are "verified" (solver ignores the path)
         - try/except AssertionError is unreachable

         Correct translation needs BOTH:
         - assert(x > 0)  → check that x > 0 holds (report if not)
         - assume(x > 0)  → for subsequent code, x > 0 is known

CPython result: AssertionError raised when condition is False
Model result: path silently pruned (no error reported)
"""


def positive_only(x: int) -> int:
    """Assert as precondition — failure should be detectable."""
    assert x > 0
    return x * 2


def bounded(x: int, lo: int, hi: int) -> int:
    """Multiple asserts as preconditions."""
    assert x >= lo
    assert x <= hi
    return x


def assert_after_computation(xs: list[int]) -> int:
    """Assert as postcondition check."""
    total: int = 0
    for x in xs:
        total += x
    assert total >= 0  # should be provable if all elements >= 0
    return total


def assert_catches_bug() -> int:
    """Assert that SHOULD fire — model must detect this."""
    x: int = -5
    assert x > 0  # THIS ALWAYS FAILS — model should report it
    return x


def main() -> None:
    # Test 1: assert passes
    assert positive_only(5) == 10

    # Test 2: assert fails
    raised: bool = False
    try:
        positive_only(-3)
    except AssertionError:
        raised = True
    assert raised

    # Test 3: bounded
    assert bounded(5, 0, 10) == 5

    # Test 4: assert after computation
    assert assert_after_computation([1, 2, 3]) == 6

    # Test 5: assert that always fails
    raised2: bool = False
    try:
        assert_catches_bug()
    except AssertionError:
        raised2 = True
    assert raised2

    print("all passed")


main()
