# **FIX: Complete operator dispatch table** — enumerate all valid (left,right)
# pairs; bool normalize; catch-all=TypeError; resolves 40+ findings
"""
FIX PROPOSAL: Complete the operator dispatch table.
Resolves findings: 018, 022, 024, 035, 043, 050, 057, 073, 074, 076,
077, 108, 109, 110, 111, 112, 145, 148, 166, 178, 201, 204, 256,
260, 261, 262, 263, 264, 265, 270, 281-285, 286, 287, 290, 294.

The fix: enumerate ALL valid (left_tag, right_tag) pairs for each
operator. Invalid pairs produce exception(TypeError). No Hole anywhere.

This program demonstrates that WITH the fix, all operations work.
"""


def arithmetic_cross_type() -> bool:
    """All cross-type arithmetic must work."""
    assert 3 + 1.5 == 4.5       # int + float
    assert 1.5 + 3 == 4.5       # float + int
    assert True + 5 == 6        # bool + int
    assert 3 * 2.5 == 7.5       # int * float
    assert 3 * "ab" == "ababab" # int * str
    assert [1] + [2] == [1, 2]  # list + list
    return True


def comparison_cross_type() -> bool:
    """All cross-type comparisons must work."""
    assert (3 < 4.5) == True    # int < float
    assert (True < 2) == True   # bool < int
    assert (0 == False) == True # int == bool
    assert (None == 0) == False # None == int (False, not error)
    return True


def not_on_all_types() -> bool:
    """`not` must handle all types via truthiness."""
    assert (not 0) == True
    assert (not 5) == False
    assert (not "") == True
    assert (not "x") == False
    assert (not None) == True
    return True


def invalid_ops_raise() -> bool:
    """Invalid type combos must raise TypeError, not Hole."""
    caught: int = 0
    try:
        "hello" + 5  # type: ignore
    except TypeError:
        caught = caught + 1
    try:
        None + 1  # type: ignore
    except TypeError:
        caught = caught + 1
    try:
        "a" < 1  # type: ignore
    except TypeError:
        caught = caught + 1
    return caught == 3


def main() -> None:
    assert arithmetic_cross_type() == True
    assert comparison_cross_type() == True
    assert not_on_all_types() == True
    assert invalid_ops_raise() == True
    print("All operator dispatch tests pass")


main()
