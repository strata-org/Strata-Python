# For loop variable persists after loop — Python scoping keeps loop var in
# enclosing scope; translator must not scope it to loop body
"""
In Python, the loop variable of a `for` loop remains in scope after the
loop exits, retaining the value from the last iteration. If the loop body
never executes (empty iterable), the variable is UNBOUND.

The Laurel model must:
1. Ensure the loop variable retains its last-iteration value after the loop
2. Handle the empty-iterable case (variable unbound → potential NameError)

Uses ONLY confirmed-accepted constructs: for loop, list, int, function def.
"""


def last_element(xs: list[int]) -> int:
    result: int = 0
    for x in xs:
        result = x
    # x is still in scope here in CPython, holding the last element
    # But we use result to avoid the unbound issue
    return result


def sum_with_last(xs: list[int]) -> int:
    total: int = 0
    last: int = 0
    for x in xs:
        total = total + x
        last = x
    # After loop: last holds the final element value
    # total + last doubles the last element
    return total + last


def index_of_last_positive(xs: list[int]) -> int:
    idx: int = -1
    i: int = 0
    for x in xs:
        if x > 0:
            idx = i
        i = i + 1
    # i after loop == len(xs) in CPython
    # Model must ensure i is incremented correctly through all iterations
    return idx


def loop_variable_used_after(xs: list[int]) -> int:
    """The loop variable x persists after the for loop in CPython."""
    x: int = -999  # default if loop doesn't execute
    for x in xs:
        pass
    # x is now the last element of xs (or -999 if xs was empty)
    return x


def main() -> None:
    assert last_element([10, 20, 30]) == 30
    assert last_element([5]) == 5
    assert last_element([]) == 0  # result stays at default

    assert sum_with_last([1, 2, 3]) == 9  # 6 + 3
    assert sum_with_last([10]) == 20  # 10 + 10

    assert index_of_last_positive([1, -2, 3, -4]) == 2
    assert index_of_last_positive([-1, -2]) == -1

    # Loop variable persists after loop
    assert loop_variable_used_after([7, 8, 9]) == 9
    assert loop_variable_used_after([]) == -999

    print(last_element([10, 20, 30]), sum_with_last([1, 2, 3]),
          loop_variable_used_after([7, 8, 9]))


main()
