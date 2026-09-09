# Compound while condition short-circuit — `while i < len(xs) and xs[i] >= 0`
# requires left-to-right eval; eager eval causes IndexError
"""
The walrus operator `:=` is OUT of the subset. But this finding tests
a related IN-subset pattern: assignment in a WHILE condition via a
helper variable.

The subset allows `while cond:` where cond is a boolean expression.
But what about patterns where the condition depends on a value computed
each iteration?

    while (line := f.readline()) != "":  ← OUT (walrus)

    line = get_next()
    while line != "":                    ← IN (pre-compute)
        process(line)
        line = get_next()

The model must handle the "loop-and-a-half" pattern where the condition
variable is updated at the END of the loop body.

Uses ONLY confirmed-accepted constructs: while, list, int, function def.
"""


def find_first_negative(xs: list[int]) -> int:
    """Loop-and-a-half: check condition, process, advance."""
    i: int = 0
    while i < len(xs) and xs[i] >= 0:
        i = i + 1
    if i < len(xs):
        return xs[i]
    return 0  # no negative found


def consume_until_zero(xs: list[int]) -> int:
    """Sum elements until hitting zero."""
    total: int = 0
    i: int = 0
    while i < len(xs):
        if xs[i] == 0:
            break
        total = total + xs[i]
        i = i + 1
    return total


def process_with_sentinel(xs: list[int]) -> int:
    """Process elements, stop at sentinel value -1."""
    count: int = 0
    i: int = 0
    while i < len(xs):
        val: int = xs[i]
        if val == -1:
            break
        count = count + 1
        i = i + 1
    return count


def main() -> None:
    assert find_first_negative([1, 2, 3, -4, 5]) == -4
    assert find_first_negative([1, 2, 3]) == 0

    assert consume_until_zero([1, 2, 3, 0, 99]) == 6
    assert consume_until_zero([5, 10, 15]) == 30

    assert process_with_sentinel([1, 2, 3, -1, 4, 5]) == 3
    assert process_with_sentinel([1, 2, 3]) == 3

    print(find_first_negative([1, -2, 3]),
          consume_until_zero([1, 2, 0, 99]),
          process_with_sentinel([1, 2, -1]))


main()
