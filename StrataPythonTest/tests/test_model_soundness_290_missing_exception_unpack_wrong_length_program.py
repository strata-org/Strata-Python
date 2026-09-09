# Missing exception: `"hello" < 5` → TypeError (ordering on incompatible
# types); PLt catch-all must be TypeError not Hole
"""
MISSING EXCEPTION: Comparison on incompatible types → TypeError.

CPython: "hello" < 5 → TypeError (unorderable types)
Model: PLt(from_str("hello"), from_int(5)) → Hole (no error)

Note: == and != work cross-type (return False). But <, >, <=, >= on
incompatible types raise TypeError in Python 3.
"""


def str_lt_int() -> bool:
    return "hello" < 5  # type: ignore — TypeError!


def list_lt_int() -> bool:
    return [1, 2] < 3  # type: ignore — TypeError!


def none_lt_int() -> bool:
    return None < 0  # type: ignore — TypeError!


def main() -> None:
    caught1: bool = False
    try:
        str_lt_int()
    except TypeError:
        caught1 = True
    assert caught1 == True

    caught2: bool = False
    try:
        list_lt_int()
    except TypeError:
        caught2 = True
    assert caught2 == True

    caught3: bool = False
    try:
        none_lt_int()
    except TypeError:
        caught3 = True
    assert caught3 == True

    print(caught1, caught2, caught3)


main()
