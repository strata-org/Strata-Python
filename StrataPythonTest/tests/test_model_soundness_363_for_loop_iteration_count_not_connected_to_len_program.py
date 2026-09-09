# For-loop iteration count not connected to `len(xs)` — no axiom says "loop
# body executes len(xs) times"; post-loop properties unprovable
"""
FOR-LOOP ITERATION COUNT NOT CONNECTED TO len(xs)

CPython: for x in xs: body
         Executes body exactly len(xs) times.
         After loop: loop variable x holds last element.

Model:   The for-loop translation iterates over the cons-list.
         But there's no axiom connecting:
         - Number of iterations to List_len(xs)
         - Loop variable's final value to the last element
         - Accumulator's final value to a function of all elements

         Without this connection, the verifier cannot prove:
         - "this loop processes all elements"
         - "the counter equals len(xs) after the loop"
         - "the sum equals the sum of all elements"

This is distinct from finding 305 (range(len(xs)) index validity)
because it's about the for-ELEMENT loop, not the for-INDEX loop.
"""


def count_elements(xs: list[int]) -> int:
    """Count should equal len(xs) — but model can't prove it."""
    count: int = 0
    for x in xs:
        count += 1
    # CPython: count == len(xs) (always)
    # Model: count is some value from loop unrolling, but
    #         no axiom says "for iterates len(xs) times"
    return count


def sum_equals_manual(xs: list[int]) -> bool:
    """Sum via loop should equal sum via manual addition."""
    total: int = 0
    for x in xs:
        total += x
    # For xs = [1, 2, 3]: total should be 6
    # Model: total is accumulated but final value unprovable
    #         without knowing iteration count == len(xs)
    return total == sum(xs)


def all_positive(xs: list[int]) -> bool:
    """Check all elements — must visit every element."""
    for x in xs:
        if x <= 0:
            return False
    # If we reach here: ALL elements were positive
    # Model: without knowing loop visits all elements,
    #         can't prove the universal property
    return True


def last_element_after_loop(xs: list[int]) -> int:
    """Loop variable holds last element after loop."""
    last: int = 0
    for x in xs:
        last = x
    # CPython: last == xs[-1] (last element)
    # Model: last is some value, but no axiom connects it to xs[-1]
    return last


def main() -> None:
    data: list[int] = [10, 20, 30, 40, 50]

    # Test 1: count equals length
    assert count_elements(data) == 5
    assert count_elements(data) == len(data)
    assert count_elements([]) == 0

    # Test 2: sum consistency
    assert sum_equals_manual(data)
    assert sum_equals_manual([])

    # Test 3: universal property
    assert all_positive([1, 2, 3])
    assert not all_positive([1, -2, 3])

    # Test 4: last element
    assert last_element_after_loop(data) == 50
    assert last_element_after_loop([7]) == 7

    print("all passed")


main()
