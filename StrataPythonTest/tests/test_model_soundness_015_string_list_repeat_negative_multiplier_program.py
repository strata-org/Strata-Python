# `string_repeat`/`List_repeat` are uninterpreted with no axioms; `s * n` for
# n ≤ 0 yields unconstrained value instead of empty
"""
Python's `str * n` and `list * n` return empty string/list when n <= 0.
The Laurel encoding uses uninterpreted functions `string_repeat` and
`List_repeat` with no postconditions, so the solver cannot prove anything
about the result when n <= 0.
"""


def repeat_string(s: str, n: int) -> str:
    return s * n


def repeat_list(xs: list[int], n: int) -> list[int]:
    return xs * n


def main() -> None:
    # CPython: "" (empty string when multiplier is negative)
    result_s: str = repeat_string("abc", -1)
    assert result_s == ""  # CPython: passes

    # CPython: [] (empty list when multiplier is 0)
    result_l: list[int] = repeat_list([1, 2], 0)
    assert len(result_l) == 0  # CPython: passes

    # CPython: [] (empty list when multiplier is negative)
    result_l2: list[int] = repeat_list([1, 2], -3)
    assert len(result_l2) == 0  # CPython: passes

    print(result_s)
    print(result_l)
    print(result_l2)


main()
