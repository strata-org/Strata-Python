# `for x in lst` — CPython snapshots iterator at entry; model may re-read
# variable, so reassigning `lst` in body diverges
"""
CPython's `for x in lst` captures an iterator at loop entry. Reassigning
the list variable inside the loop does NOT affect iteration — the iterator
holds a reference to the ORIGINAL list object. In the pure-functional
model, if the loop reads from the current value of the variable at each
step, reassignment inside the body changes what the loop iterates over.
"""


def collect_with_reassign(xs: list[int]) -> list[int]:
    result: list[int] = []
    for x in xs:
        result.append(x)
        if x == 1:
            xs = [99, 98, 97]  # reassign xs
    # CPython: iterates [1, 2, 3] (original), ignores reassignment
    # Model: may iterate [1, 99, 98, 97] if it reads current xs
    return result


def sum_with_clear(xs: list[int]) -> int:
    total: int = 0
    for x in xs:
        total = total + x
        xs = []  # clear xs — CPython still iterates original
    return total


def main() -> None:
    nums: list[int] = [1, 2, 3]

    collected: list[int] = collect_with_reassign(nums)
    # CPython: [1, 2, 3] — iterator snapshots the original list
    assert len(collected) == 3
    assert collected[0] == 1
    assert collected[1] == 2
    assert collected[2] == 3

    s: int = sum_with_clear([10, 20, 30])
    # CPython: 60 — iterates all three despite xs = [] each time
    assert s == 60

    print(collected, s)


main()
