# Incorrect `==` bool×int: CPython `0==False`→True, Model→Hole — separate tags
# prevent cross-type equality
"""
INCORRECT OPERATOR BEHAVIOR: == between bool and int.

CPython: 0 == False → True (because False IS 0)
         1 == True  → True (because True IS 1)
         2 == True  → False (2 != 1)
Model:   PEq(from_int(0), from_bool(False)) → Hole (cross-tag, no case)

The model can't determine that 0 equals False or 1 equals True.
"""


def zero_eq_false() -> bool:
    return 0 == False  # True (False is 0)


def one_eq_true() -> bool:
    return 1 == True  # True (True is 1)


def two_eq_true() -> bool:
    return 2 == True  # False (2 != 1)


def bool_in_int_list() -> bool:
    """True is found in [0, 1, 2] because True == 1."""
    return True in [0, 1, 2]  # True


def false_eq_zero_in_condition() -> str:
    """Common pattern: checking if value is falsy via == False."""
    x: int = 0
    if x == False:
        return "falsy"
    return "truthy"


def main() -> None:
    assert zero_eq_false() == True
    assert one_eq_true() == True
    assert two_eq_true() == False
    assert bool_in_int_list() == True
    assert false_eq_zero_in_condition() == "falsy"

    print(zero_eq_false(), one_eq_true(), two_eq_true())


main()
