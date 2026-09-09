# Missing exception: `d["missing"]` → KeyError; model returns Hole (some
# value); must check key presence
"""
MISSING EXCEPTION: d["missing_key"] → KeyError in CPython, Hole in model.

CPython: accessing a key not in the dict raises KeyError.
Model: DictStrAny_get(d, "missing") → Hole (unconstrained, no error)

The model thinks accessing a missing key MIGHT SUCCEED and return some value.
"""


def access_missing_key() -> int:
    d: dict[str, int] = {"a": 1, "b": 2}
    return d["c"]  # KeyError! "c" not in d


def access_empty_dict() -> int:
    d: dict[str, int] = {}
    return d["anything"]  # KeyError! dict is empty


def access_after_del() -> int:
    d: dict[str, int] = {"x": 10}
    del d["x"]
    return d["x"]  # KeyError! key was deleted


def main() -> None:
    caught1: bool = False
    try:
        access_missing_key()
    except KeyError:
        caught1 = True
    assert caught1 == True

    caught2: bool = False
    try:
        access_empty_dict()
    except KeyError:
        caught2 = True
    assert caught2 == True

    caught3: bool = False
    try:
        access_after_del()
    except KeyError:
        caught3 = True
    assert caught3 == True

    print(caught1, caught2, caught3)


main()
