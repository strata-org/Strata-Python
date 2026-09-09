# `len([1,2,3]) == 3` unprovable — List_len uninterpreted; blocks ALL bounds
# checking; needs SMT Array or concrete definitions
"""
LIST LITERAL LEN — UNPROVABLE WITHOUT AXIOMS

CPython: len([1, 2, 3]) == 3 → True (always)
         len([]) == 0 → True (always)

Model:   [1, 2, 3] translates to cons(1, cons(2, cons(3, nil)))
         List_len(cons(1, cons(2, cons(3, nil)))) == 3
         → UNPROVABLE if List_len is uninterpreted

         Even with List_len(nil) == 0 and List_len(cons(h,t)) == 1 + List_len(t):
         The solver needs to UNFOLD the definition 3 times.
         Without concrete definitions or axioms: len is unconstrained.

CPython result: 3
Model result: unconstrained

Root cause: List_len is uninterpreted with no axioms (finding 088/275).
"""


def literal_len_zero() -> bool:
    """len([]) == 0."""
    return len([]) == 0


def literal_len_three() -> bool:
    """len([1,2,3]) == 3."""
    xs: list[int] = [1, 2, 3]
    return len(xs) == 3


def len_after_build() -> bool:
    """Build list, check length."""
    xs: list[int] = []
    xs.append(10)
    xs.append(20)
    # len should be 2
    return len(xs) == 2


def len_in_condition(xs: list[int]) -> str:
    """Use len in condition — common pattern."""
    if len(xs) == 0:
        return "empty"
    elif len(xs) == 1:
        return "single"
    else:
        return "multiple"


def len_bounds_check(xs: list[int], i: int) -> int:
    """Bounds check using len — must be provable."""
    if i >= 0 and i < len(xs):
        return xs[i]
    return -1


def main() -> None:
    assert literal_len_zero()
    assert literal_len_three()
    assert len_after_build()

    assert len_in_condition([]) == "empty"
    assert len_in_condition([1]) == "single"
    assert len_in_condition([1, 2]) == "multiple"

    assert len_bounds_check([10, 20, 30], 1) == 20
    assert len_bounds_check([10, 20, 30], 5) == -1

    print("all passed")


main()
