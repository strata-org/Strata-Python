# While + break postcondition — after break, assume the BREAK GUARD (not
# negated loop condition); finding 311's fix
"""
WHILE TRUE + BREAK — POSTCONDITION FROM BREAK GUARD

CPython: while True:
             if found: break
         # After loop: `found` is True (break only exits when found is True)

Model:   Finding 311 notes that `assume(!condition)` after while is UNSOUND
         when break exits (condition is still True).

         But the BREAK GUARD gives us information:
         `if cond: break` means: at the break point, cond is True.
         After the loop (exited via break): cond holds.

         The model must emit: assume(break_guard_condition) after the loop
         (when the loop can ONLY exit via break, not normal termination).

For `while True: ... if cond: break`:
  - Normal exit: impossible (True is always True)
  - Break exit: cond is True at break point
  - Post-loop: assume(cond)
"""


def find_first_positive(xs: list[int]) -> int:
    """while True + break — post-loop knows element was found."""
    i: int = 0
    result: int = -1
    while i < len(xs):
        if xs[i] > 0:
            result = xs[i]
            break
        i += 1
    # If we broke: result > 0 (from the break guard)
    # If loop ended normally: result == -1
    return result


def binary_search_step(xs: list[int], target: int) -> int:
    """Search with while + break — post-loop knows target found or exhausted."""
    lo: int = 0
    hi: int = len(xs) - 1
    result: int = -1
    while lo <= hi:
        mid: int = (lo + hi) // 2
        if xs[mid] == target:
            result = mid
            break
        elif xs[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return result


def read_until_sentinel(xs: list[int]) -> int:
    """Process until sentinel value found."""
    total: int = 0
    i: int = 0
    while i < len(xs):
        if xs[i] == 0:
            break  # sentinel found
        total += xs[i]
        i += 1
    # After break: xs[i] == 0 (the sentinel)
    # After normal exit: processed all elements
    return total


def main() -> None:
    # Test 1: find first positive
    assert find_first_positive([-1, -2, 3, 4]) == 3
    assert find_first_positive([-1, -2, -3]) == -1

    # Test 2: binary search
    assert binary_search_step([1, 3, 5, 7, 9], 5) == 2
    assert binary_search_step([1, 3, 5, 7, 9], 4) == -1

    # Test 3: read until sentinel
    assert read_until_sentinel([1, 2, 3, 0, 99]) == 6  # 1+2+3
    assert read_until_sentinel([5, 10, 15]) == 30  # no sentinel

    print("all passed")


main()
