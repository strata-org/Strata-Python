# Ordering comparisons (`<`, `>`, `<=`, `>=`) on bool×int or bool×bool —
# `PLt`/`PGt` don't normalize, falls to Hole
"""
Python comparison operators (<, <=, >, >=, ==, !=) work across bool and int
because bool is a subclass of int. True > 0 is True, False < 1 is True, etc.
The Laurel PLt/PGt/PLe/PGe operators dispatch on tags — if they only handle
from_int × from_int and from_bool × from_bool but not the cross-type case,
comparisons between bool and int values produce Hole or wrong results.
"""


def is_positive_flag(flag: bool) -> bool:
    # True > 0 should be True (1 > 0)
    # False > 0 should be False (0 > 0)
    return flag > 0


def compare_with_threshold(flag: bool, threshold: int) -> bool:
    # Common pattern: compare a boolean (used as 0/1) with an int
    return flag >= threshold


def sort_key(flag: bool) -> int:
    # Using comparison result in arithmetic context
    if flag > False:
        return 1
    return 0


def main() -> None:
    # bool > int comparisons
    assert is_positive_flag(True) == True    # 1 > 0 = True
    assert is_positive_flag(False) == False  # 0 > 0 = False

    # bool >= int
    assert compare_with_threshold(True, 1) == True   # 1 >= 1
    assert compare_with_threshold(True, 2) == False  # 1 >= 2
    assert compare_with_threshold(False, 0) == True  # 0 >= 0
    assert compare_with_threshold(False, 1) == False # 0 >= 1

    # bool > bool (uses int comparison: True=1, False=0)
    assert (True > False) == True   # 1 > 0
    assert (False > True) == False  # 0 > 1
    assert (True >= True) == True   # 1 >= 1

    print("all passed")


main()
