# For-loop break vs default — variable has two possible values at exit; needs
# phi-node merge: `ite(broke, break_val, default_val)`
"""
FOR LOOP BREAK VALUE VS DEFAULT VALUE — PHI/MERGE AT LOOP EXIT

CPython: result = -1
         for x in xs:
             if x > 0:
                 result = x
                 break
         # result is EITHER -1 (no break) OR first positive (break)

Model:   After the loop, `result` has TWO possible values:
         - The default (-1) if loop completed without break
         - The break-point value (first positive x) if break executed

         The model must MERGE these two paths correctly.
         Without proper merge: result is either always -1 (break lost)
         or always the break value (default lost).

This is the PHI-NODE problem at loop exit: the variable has different
values depending on which path exited the loop.
"""


def find_first_positive(xs: list[int]) -> int:
    """Classic search pattern: default + break."""
    result: int = -1
    for x in xs:
        if x > 0:
            result = x
            break
    return result


def find_index(xs: list[int], target: int) -> int:
    """Find index with default -1."""
    idx: int = -1
    i: int = 0
    for x in xs:
        if x == target:
            idx = i
            break
        i += 1
    return idx


def has_negative(xs: list[int]) -> bool:
    """Boolean search: found or not found."""
    found: bool = False
    for x in xs:
        if x < 0:
            found = True
            break
    return found


def sum_until_zero(xs: list[int]) -> int:
    """Accumulate until sentinel, return accumulated value."""
    total: int = 0
    for x in xs:
        if x == 0:
            break
        total += x
    return total


def main() -> None:
    # Test 1: found (break path)
    assert find_first_positive([-1, -2, 3, 4]) == 3

    # Test 2: not found (default path)
    assert find_first_positive([-1, -2, -3]) == -1

    # Test 3: find index
    assert find_index([10, 20, 30], 20) == 1
    assert find_index([10, 20, 30], 99) == -1

    # Test 4: boolean search
    assert has_negative([1, -2, 3])
    assert not has_negative([1, 2, 3])

    # Test 5: sum until sentinel
    assert sum_until_zero([1, 2, 3, 0, 99]) == 6
    assert sum_until_zero([5, 10, 15]) == 30  # no sentinel

    print("all passed")


main()
