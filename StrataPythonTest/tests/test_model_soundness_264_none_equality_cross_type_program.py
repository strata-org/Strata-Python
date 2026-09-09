# Cross-type equality: `None==None`→True, `None==0`→False, `0==False`→True —
# PEq has no cross-tag cases; all return Hole
"""
CPython results (concrete):
  None == None  = True
  None == 0     = False
  None == False = False
  None == ""    = False
  0 == False    = True  (bool is int subclass!)
  1 == True     = True

Laurel model results:
  PEq(from_None(), from_None())    = ??? (may be Hole if no None×None case)
  PEq(from_None(), from_int(0))    = ??? (cross-tag: Hole or wrong)
  PEq(from_int(0), from_bool(False)) = ??? (cross-tag: Hole)
  PEq(from_int(1), from_bool(True))  = ??? (cross-tag: Hole)
"""


def none_eq_none() -> bool:
    return None == None  # True


def none_eq_zero() -> bool:
    return None == 0  # False


def none_eq_false() -> bool:
    return None == False  # False


def none_eq_empty_str() -> bool:
    return None == ""  # False


def zero_eq_false() -> bool:
    return 0 == False  # True (bool subclass of int)


def one_eq_true() -> bool:
    return 1 == True  # True (bool subclass of int)


def two_eq_true() -> bool:
    return 2 == True  # False (2 != 1)


def main() -> None:
    # CPython concrete results:
    assert none_eq_none() == True
    assert none_eq_zero() == False
    assert none_eq_false() == False
    assert none_eq_empty_str() == False
    assert zero_eq_false() == True
    assert one_eq_true() == True
    assert two_eq_true() == False

    print(none_eq_none(), none_eq_zero(), zero_eq_false(), one_eq_true())


main()
