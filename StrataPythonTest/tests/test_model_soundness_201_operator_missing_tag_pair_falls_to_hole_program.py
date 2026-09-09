# Operator missing tag pair falls to Hole — ~15 valid cross-type pairs
# (int+float, int*str, list+list, etc.) have no case; comprehensive catalog
"""
Operators pattern-match on (left_tag, right_tag). If a valid type pair
has no matching case, the result is Hole — an unconstrained value that
silently propagates. CPython would either compute a correct result or
raise TypeError.

This finding provides a CATALOG of valid type pairs that likely have
no case in the model, producing Hole where CPython produces a value.

The subset allows: int, float, bool, str, None, list, dict, ClassInstance.
Valid operator pairs (non-exhaustive):
  + : (int,int), (float,float), (int,float), (float,int), (str,str), (list,list)
  * : (int,int), (float,float), (int,float), (str,int), (int,str)
  - : (int,int), (float,float), (int,float), (float,int)
  / : (int,int), (int,float), (float,int), (float,float)
  //: (int,int), (float,float), (int,float), (float,int)
  % : (int,int), (float,float), (int,float), (float,int)
  ==: ALL pairs (cross-type returns False except int/float/bool)
  < : (int,int), (float,float), (int,float), (float,int), (str,str)

Uses ONLY confirmed-accepted constructs: int, float, str, arithmetic.
"""


def int_float_add(a: int, b: float) -> float:
    return a + b  # 3 + 1.5 = 4.5


def float_int_sub(a: float, b: int) -> float:
    return a - b  # 5.5 - 2 = 3.5


def int_float_mul(a: int, b: float) -> float:
    return a * b  # 3 * 2.5 = 7.5


def float_int_div(a: float, b: int) -> float:
    return a / b  # 10.0 / 4 = 2.5


def int_float_floor_div(a: int, b: float) -> float:
    return a // b  # 7 // 2.0 = 3.0


def int_float_mod(a: int, b: float) -> float:
    return a % b  # 7 % 2.5 = 2.0


def str_str_add(a: str, b: str) -> str:
    return a + b  # "hello" + " world"


def int_str_mul(n: int, s: str) -> str:
    return n * s  # 3 * "ab" = "ababab"


def list_list_add(a: list[int], b: list[int]) -> list[int]:
    return a + b  # [1,2] + [3,4] = [1,2,3,4]


def all_cross_type_ops() -> bool:
    """Verify all cross-type operations produce correct results."""
    assert int_float_add(3, 1.5) == 4.5
    assert float_int_sub(5.5, 2) == 3.5
    assert int_float_mul(3, 2.5) == 7.5
    assert float_int_div(10.0, 4) == 2.5
    assert int_float_floor_div(7, 2.0) == 3.0
    assert int_float_mod(7, 2.5) == 2.0
    assert str_str_add("hello", " world") == "hello world"
    assert int_str_mul(3, "ab") == "ababab"
    assert list_list_add([1, 2], [3, 4]) == [1, 2, 3, 4]
    return True


def main() -> None:
    assert all_cross_type_ops() == True
    print(int_float_add(3, 1.5), float_int_sub(5.5, 2),
          int_str_mul(3, "ab"))


main()
