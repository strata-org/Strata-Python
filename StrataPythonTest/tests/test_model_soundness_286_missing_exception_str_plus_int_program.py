# Missing exception: `"hello" + 5` → TypeError in CPython, Hole in model;
# catch-all must be exception not Hole
"""
MISSING EXCEPTION: "hello" + 5 → TypeError in CPython, Hole in model.

CPython: str.__add__(int) → TypeError (can't concatenate str and int)
Model: PAdd(from_str("hello"), from_int(5)) → Hole (catch-all, no error)

The model should produce exception(TypeError) but produces Hole instead.
This means the model thinks "hello" + 5 MIGHT SUCCEED.
"""


def str_plus_int() -> str:
    return "hello" + 5  # type: ignore — TypeError!


def str_minus_str() -> str:
    return "hello" - "h"  # type: ignore — TypeError!


def none_times_int() -> int:
    return None * 3  # type: ignore — TypeError!


def main() -> None:
    caught1: bool = False
    try:
        str_plus_int()
    except TypeError:
        caught1 = True
    assert caught1 == True  # CPython raises TypeError

    caught2: bool = False
    try:
        str_minus_str()
    except TypeError:
        caught2 = True
    assert caught2 == True

    caught3: bool = False
    try:
        none_times_int()
    except TypeError:
        caught3 = True
    assert caught3 == True

    print(caught1, caught2, caught3)


main()
