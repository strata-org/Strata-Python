# `isinstance(True, int)` returns True — bool⊂int; model's tag check
# `isfrom_int` misses `from_bool` values
"""
`isinstance(True, int)` returns True in CPython because bool is a
subclass of int. The model's isinstance likely checks the tag:
- isfrom_int(from_bool(true)) → False (different tag!)
- But CPython says True IS an int.

This means isinstance(x, int) must return True for BOTH from_int AND
from_bool values. The model must handle the bool⊂int relationship.
"""


def is_integer(x: int) -> bool:
    return isinstance(x, int)


def count_ints(values: list[int]) -> int:
    count: int = 0
    for v in values:
        if isinstance(v, int):
            count = count + 1
    return count


def check_bool_is_int() -> bool:
    t: bool = True
    f: bool = False
    # Both are instances of int
    return isinstance(t, int) and isinstance(f, int)


def main() -> None:
    # Regular int
    assert isinstance(5, int) == True
    assert isinstance(0, int) == True

    # Bool IS int (subclass)
    assert isinstance(True, int) == True
    assert isinstance(False, int) == True

    # Check function
    assert check_bool_is_int() == True

    # Count: bools count as ints
    assert is_integer(42) == True

    print(isinstance(True, int), isinstance(5, int), check_bool_is_int())


main()
