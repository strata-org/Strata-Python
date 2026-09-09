# Cons-list index access axiom completeness — solver can't prove
# `[1,2,3][0]==1` without postconditions or array-theory encoding
"""
Cons-lists have O(n) index access: `List_get(lst, i)` must traverse
i cons cells to reach element i. CPython lists have O(1) random access
(array-backed).

This doesn't affect CORRECTNESS but affects AXIOM DESIGN. The key issue:
if `List_get` is defined recursively on the cons structure, the solver
must unfold the recursion to prove properties about specific indices.

For VERIFICATION, the critical question is: can the solver prove
`lst[i] == expected` after a sequence of operations? This requires
the axioms to be COMPLETE enough that the solver can determine the
value at any index after construction/modification.

The specific gap: after `lst = [1, 2, 3]` (literal construction),
can the solver prove `lst[0] == 1`? This requires the literal
construction to emit postconditions for EACH index.

Finding 089 identified cons-order issues. This finding focuses on
whether the axioms are SUFFICIENT for index-based reasoning.

Uses ONLY confirmed-accepted constructs: list, int, indexing, function def.
"""


def access_literal_elements() -> int:
    """Access elements of a literal — requires construction postconditions."""
    xs: list[int] = [10, 20, 30, 40, 50]
    return xs[0] + xs[2] + xs[4]  # 10 + 30 + 50 = 90


def access_after_append() -> int:
    """After append, new element is at index len-1."""
    xs: list[int] = [1, 2, 3]
    xs.append(4)
    # xs[3] must be 4 (the appended element)
    # xs[0] must still be 1 (unchanged)
    return xs[3] + xs[0]  # 4 + 1 = 5


def access_after_assignment() -> int:
    """After xs[i] = v, reading xs[i] must give v."""
    xs: list[int] = [10, 20, 30]
    xs[1] = 99
    # xs[1] must be 99
    # xs[0] must still be 10
    # xs[2] must still be 30
    return xs[0] + xs[1] + xs[2]  # 10 + 99 + 30 = 139


def index_in_loop() -> int:
    """Access by computed index in a loop."""
    xs: list[int] = [5, 10, 15, 20, 25]
    total: int = 0
    i: int = 0
    while i < len(xs):
        total = total + xs[i]
        i = i + 1
    return total  # 75


def reverse_access(xs: list[int]) -> list[int]:
    """Read elements in reverse order."""
    result: list[int] = []
    i: int = len(xs) - 1
    while i >= 0:
        result.append(xs[i])
        i = i - 1
    return result


def main() -> None:
    # Literal access
    assert access_literal_elements() == 90

    # After append
    assert access_after_append() == 5

    # After assignment
    assert access_after_assignment() == 139

    # Loop access
    assert index_in_loop() == 75

    # Reverse
    assert reverse_access([1, 2, 3]) == [3, 2, 1]
    assert reverse_access([]) == []

    print(access_literal_elements(), access_after_append(),
          access_after_assignment())


main()
