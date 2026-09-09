# **ROOT CAUSE: Incomplete tag dispatch** — operators only handle same-type
# pairs; 30+ findings from missing cross-type cases
"""
ROOT CAUSE: Operators dispatch by pattern matching on (left_tag, right_tag).
PROPERTY: No slot lookup. No reflected methods. Incomplete case coverage.

This single property causes findings:
018, 022, 024, 035, 043, 050, 057, 073, 074, 076, 077, 108, 109,
110, 111, 112, 145, 148, 166, 178, 201, 204, 256, 260, 261, 262,
263, 264, 265, 270.

DEMONSTRATION: Operations on valid type combinations return Hole.
"""


def int_float_ops() -> float:
    """int × float: valid in CPython, Hole in model."""
    return 3 + 1.5  # PAdd(from_int, from_float) → Hole


def bool_int_ops() -> int:
    """bool × int: valid in CPython (bool⊂int), Hole in model."""
    return True + 5  # PAdd(from_bool, from_int) → Hole


def int_str_ops() -> str:
    """int × str: valid in CPython (reflected), Hole in model."""
    return 3 * "ab"  # PMul(from_int, from_str) → Hole


def list_concat() -> list[int]:
    """list + list: valid in CPython, Hole in model."""
    return [1, 2] + [3, 4]  # PAdd(from_ListAny, from_ListAny) → Hole


def none_arithmetic() -> int:
    """None + int: TypeError in CPython, Hole in model (should be exception)."""
    try:
        x = None + 1  # type: ignore
        return 0
    except TypeError:
        return -1


def cross_type_eq() -> bool:
    """None == 0: False in CPython, Hole in model."""
    return None == 0  # PEq(from_None, from_int) → Hole (should be False)


def main() -> None:
    assert int_float_ops() == 4.5
    assert bool_int_ops() == 6
    assert int_str_ops() == "ababab"
    assert list_concat() == [1, 2, 3, 4]
    assert none_arithmetic() == -1
    assert cross_type_eq() == False

    print(int_float_ops(), bool_int_ops(), int_str_ops())


main()
