# `[1,2,3][5]`: CPython=IndexError, Model=Hole — no bounds check; model misses
# out-of-bounds crash; unsound
"""
CPython: [1,2,3][5] → IndexError (program crashes)
Model:   List_get(lst, 5) = from_int(???) or Hole ← NO ERROR

If List_get has no bounds check, accessing an out-of-bounds index
either returns Hole (unconstrained) or an arbitrary value — but
does NOT produce an exception. CPython CRASHES.

The model says "this might work" when CPython says "this crashes."
"""


def index_out_of_bounds() -> int:
    """CPython: IndexError. Model: no error."""
    xs: list[int] = [1, 2, 3]
    return xs[5]  # index 5, but list has only 3 elements


def negative_too_far() -> int:
    """CPython: IndexError. Model: no error."""
    xs: list[int] = [10, 20, 30]
    return xs[-4]  # -4 wraps to index -1 (len=3, -4+3=-1 < 0 → error)


def empty_list_access() -> int:
    """CPython: IndexError. Model: no error."""
    xs: list[int] = []
    return xs[0]  # empty list, any index is out of bounds


def main() -> None:
    # All three MUST raise IndexError
    caught1: bool = False
    try:
        index_out_of_bounds()
    except IndexError:
        caught1 = True
    assert caught1 == True

    caught2: bool = False
    try:
        negative_too_far()
    except IndexError:
        caught2 = True
    assert caught2 == True

    caught3: bool = False
    try:
        empty_list_access()
    except IndexError:
        caught3 = True
    assert caught3 == True

    print(caught1, caught2, caught3)


main()
