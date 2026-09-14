"""A non-integral index into a builtin sequence is a TypeError, not a bounds miss.

Five branches of `itemRead` each carried their own copy of one rule -- integral
index gives the element plus a bounds obligation plus IndexError, non-integral
gives TypeError -- and `tuple` omitted the index-type half. `t[s]` reported
IndexError and no TypeError, where CPython raises TypeError and never IndexError:
wrong in both directions at once.

No golden exercised it, which is why five copies of the rule could disagree
unnoticed. The rule is one table row per tag now, and this pins every tag.
"""


def tuple_str_index(t: tuple[int, str], s: str) -> object:
    return t[s]


def list_str_index(xs: list[int], s: str) -> object:
    return xs[s]


def str_str_index(text: str, s: str) -> object:
    return text[s]


def bytes_str_index(text: str, s: str) -> object:
    return text.encode()[s]


def range_str_index(n: int, s: str) -> object:
    return range(n)[s]


def tuple_literal_index(t: tuple[int, str]) -> int:
    # A literal index with a known slot is exact: no bounds question and no
    # index-type question, because the index *is* that literal.
    return t[0]


def integral_indices(t: tuple[int, str], xs: list[int], n: int) -> object:
    return (t[n], xs[n], range(n)[n])


def union_index_raises_both(t: tuple[int, str], k: int | str) -> object:
    # The case that distinguishes a correct fix from an `if/else`. CPython checks
    # the index type before any bounds check, so `t["1"]` is a TypeError even on
    # an empty tuple, and IndexError only ever comes from an in-type int that is
    # out of range. With an `int | str` index both are reachable, from different
    # parts of the value, so both must be reported and neither may suppress the
    # other. The two arms are independent tests over the index's tag set.
    return t[k]


def union_index_list(xs: list[int], k: int | str) -> object:
    return xs[k]
