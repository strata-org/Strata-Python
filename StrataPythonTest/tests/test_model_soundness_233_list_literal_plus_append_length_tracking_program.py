# List literal + append length tracking — solver needs CONNECTED axioms:
# literal postcondition + append len+1 + preservation; chain breaks if any
# missing
"""
After constructing a list literal and appending elements, the model must
track the list's length precisely. The solver needs to prove:
  len([1,2,3]) == 3
  After append: len == 4
  After another append: len == 5

This requires CONNECTED axioms between:
- List literal construction (finding 183: postconditions)
- List_append (finding 170: rebind + len+1)
- List_len (finding 088: no relationship to operations)

Without all three working together, loop bounds and index checks fail.

Uses ONLY confirmed-accepted constructs: list, append, len, int, while.
"""


def build_and_check_length() -> bool:
    xs: list[int] = [1, 2, 3]
    # len(xs) == 3
    xs.append(4)
    # len(xs) == 4
    xs.append(5)
    # len(xs) == 5
    return len(xs) == 5


def build_in_loop_check_length(n: int) -> bool:
    xs: list[int] = []
    i: int = 0
    while i < n:
        xs.append(i)
        i = i + 1
    # After loop: len(xs) == n
    return len(xs) == n


def index_after_append() -> int:
    xs: list[int] = []
    xs.append(10)
    xs.append(20)
    xs.append(30)
    # xs[0]==10, xs[1]==20, xs[2]==30, len==3
    # Access last element by index
    return xs[len(xs) - 1]  # 30


def safe_access_after_build(n: int) -> int:
    """Build list, then access — bounds must be provable."""
    xs: list[int] = []
    i: int = 0
    while i < n:
        xs.append(i * 10)
        i = i + 1
    # len(xs) == n (from loop invariant)
    if n > 0:
        return xs[0]  # safe: len >= 1
    return -1


def main() -> None:
    assert build_and_check_length() == True
    assert build_in_loop_check_length(5) == True
    assert build_in_loop_check_length(0) == True
    assert index_after_append() == 30
    assert safe_access_after_build(3) == 0
    assert safe_access_after_build(0) == -1

    print(build_and_check_length(), build_in_loop_check_length(5),
          index_after_append())


main()
