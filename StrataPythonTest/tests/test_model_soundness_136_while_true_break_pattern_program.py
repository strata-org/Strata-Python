# `while True: ... break` — loop termination depends solely on break
# reachability; requires finding 054 fix + termination measure
"""
`while True: ... break` is a common pattern for loops with exit
conditions in the middle. The model must handle:
1. `True` as a loop condition (always truthy — loop never exits via condition)
2. `break` as the only exit mechanism
3. Termination depends on reaching the break

If the model can't prove the break is reachable, it may report
non-termination. If break is dropped (finding 054), the loop is infinite.
"""


def read_until_zero(values: list[int]) -> int:
    """Sum values until zero is encountered."""
    total: int = 0
    i: int = 0
    while True:
        if i >= len(values):
            break
        if values[i] == 0:
            break
        total = total + values[i]
        i = i + 1
    return total


def find_first_match(lst: list[int], target: int) -> int:
    """Return index of target, or -1."""
    i: int = 0
    while True:
        if i >= len(lst):
            return -1
        if lst[i] == target:
            return i
        i = i + 1
    # Unreachable — but model must know this


def retry_until_success(max_attempts: int) -> int:
    """Simulate retry loop."""
    attempt: int = 0
    while True:
        attempt = attempt + 1
        if attempt >= max_attempts:
            break
    return attempt


def main() -> None:
    # Sum until zero
    assert read_until_zero([1, 2, 3, 0, 4, 5]) == 6
    assert read_until_zero([0, 1, 2]) == 0
    assert read_until_zero([1, 2, 3]) == 6  # no zero, hits len

    # Find first match
    assert find_first_match([10, 20, 30, 40], 30) == 2
    assert find_first_match([10, 20, 30], 99) == -1

    # Retry
    assert retry_until_success(5) == 5

    print(read_until_zero([1, 2, 3, 0]), find_first_match([1, 2, 3], 2))


main()
