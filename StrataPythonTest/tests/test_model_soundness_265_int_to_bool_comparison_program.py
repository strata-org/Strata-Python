# Bool/int comparison: `True < 2`→True — PLt has no bool×int case; must
# normalize bool to int before comparing
"""
CPython results (concrete):
  True < 2   = True  (1 < 2)
  False < 1  = True  (0 < 1)
  True > 0   = True  (1 > 0)
  True >= 1  = True  (1 >= 1)
  False >= 1 = False (0 >= 1)

Laurel model results:
  PLt(from_bool(True), from_int(2)) = Hole (no bool×int case)
"""


def bool_lt_int(a: bool, b: int) -> bool:
    return a < b


def int_lt_bool(a: int, b: bool) -> bool:
    return a < b


def bool_ge_int(a: bool, b: int) -> bool:
    return a >= b


def main() -> None:
    # CPython: True (=1) < 2 → True
    assert bool_lt_int(True, 2) == True
    # CPython: True (=1) < 1 → False
    assert bool_lt_int(True, 1) == False
    # CPython: False (=0) < 1 → True
    assert bool_lt_int(False, 1) == True

    # CPython: 0 < True (=1) → True
    assert int_lt_bool(0, True) == True
    # CPython: 1 < True (=1) → False
    assert int_lt_bool(1, True) == False

    # CPython: True (=1) >= 1 → True
    assert bool_ge_int(True, 1) == True
    # CPython: False (=0) >= 1 → False
    assert bool_ge_int(False, 1) == False

    print(bool_lt_int(True, 2), int_lt_bool(0, True),
          bool_ge_int(True, 1))


main()
