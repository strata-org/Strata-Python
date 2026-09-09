# Missing exception: `lst[1.5]` → TypeError (non-int index); model has no
# index-type validation
"""
MISSING EXCEPTION: "hello"[1.5] → TypeError in CPython, Hole in model.

CPython: str indices must be integers. Float index → TypeError.
Model: Any_get!(from_str("hello"), from_float(1.5)) → Hole (no error)

Also: list[float_index] → TypeError.
"""


def str_float_index() -> str:
    s: str = "hello"
    return s[1.5]  # type: ignore — TypeError!


def list_float_index() -> int:
    xs: list[int] = [10, 20, 30]
    return xs[1.5]  # type: ignore — TypeError!


def list_str_index() -> int:
    xs: list[int] = [10, 20, 30]
    return xs["1"]  # type: ignore — TypeError!


def main() -> None:
    caught1: bool = False
    try:
        str_float_index()
    except TypeError:
        caught1 = True
    assert caught1 == True

    caught2: bool = False
    try:
        list_float_index()
    except TypeError:
        caught2 = True
    assert caught2 == True

    caught3: bool = False
    try:
        list_str_index()
    except TypeError:
        caught3 = True
    assert caught3 == True

    print(caught1, caught2, caught3)


main()
