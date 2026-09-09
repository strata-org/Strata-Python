# Exception stored in container — `lst.append(raise())` stores exception as
# element; zombie value in list, len increases
"""
EXCEPTION STORED IN CONTAINER — EXCEPTION VALUE IN LIST/DICT

CPython: lst.append(might_raise(-1)) → raises, append never happens.
Model:   lst.append(exception(...)) → exception stored AS ELEMENT in list!
         Later: lst[0] → returns exception value
         lst[0] + 1 → PAdd(exception, int) → Hole

The exception becomes a "zombie" element in the container.
It doesn't propagate — it sits in the list waiting to infect
any code that reads it out.

Even worse: len(lst) increases (the exception IS an element),
so the list appears to have grown successfully.
"""


def might_raise(x: int) -> int:
    if x < 0:
        raise ValueError("negative")
    return x


def exception_in_append() -> list[int]:
    """Exception value appended to list."""
    xs: list[int] = [1, 2, 3]
    xs.append(might_raise(-1))
    # CPython: raises, xs stays [1, 2, 3]
    # Model: xs becomes [1, 2, 3, exception(...)] — len is 4!
    return xs


def exception_in_list_literal() -> list[int]:
    """Exception in list literal construction."""
    xs: list[int] = [might_raise(1), might_raise(-1), might_raise(3)]
    # CPython: second element raises, list never constructed
    # Model: [from_int(1), exception(...), from_int(3)] — partially constructed!
    return xs


def sum_with_exception_element() -> int:
    """Sum a list that contains an exception element."""
    xs: list[int] = [1, 2, 3]
    xs.append(might_raise(-1))
    # CPython: raises at append, sum never reached
    # Model: xs has exception element, sum iterates over it
    total: int = 0
    for x in xs:
        total += x  # when x is exception: PAdd(total, exception) → Hole
    return total


def exception_in_dict_value() -> dict[str, int]:
    """Exception as dict value."""
    d: dict[str, int] = {}
    d["a"] = might_raise(1)
    d["b"] = might_raise(-1)
    # CPython: second assignment raises, d only has "a"
    # Model: d has {"a": 1, "b": exception(...)}
    return d


def main() -> None:
    # Test 1: exception in append
    raised: bool = False
    try:
        exception_in_append()
    except ValueError:
        raised = True
    assert raised

    # Test 2: exception in list literal
    raised2: bool = False
    try:
        exception_in_list_literal()
    except ValueError:
        raised2 = True
    assert raised2

    # Test 3: sum with exception
    raised3: bool = False
    try:
        sum_with_exception_element()
    except ValueError:
        raised3 = True
    assert raised3

    # Test 4: exception in dict value
    raised4: bool = False
    try:
        exception_in_dict_value()
    except ValueError:
        raised4 = True
    assert raised4

    print("all passed")


main()
