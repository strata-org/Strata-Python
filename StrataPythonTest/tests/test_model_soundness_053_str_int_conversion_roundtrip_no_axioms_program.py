# `str(int)` and `int(str)` conversions have no axioms — roundtrip
# `int(str(n)) == n` is unprovable
"""
Python's `str()` on an int produces the decimal string representation.
`int()` on a string parses it. These conversions have precise semantics:
str(42) == "42", int("42") == 42, str(-3) == "-3", len(str(n)) depends
on the number of digits. The Laurel model's `to_str_any`/`to_int_any`
are likely uninterpreted (Hole), meaning properties like
`int(str(n)) == n` or `len(str(n)) > 0` are unprovable.
"""


def int_to_str(n: int) -> str:
    return str(n)


def roundtrip(n: int) -> int:
    s: str = str(n)
    return int(s)


def str_concat_int(label: str, value: int) -> str:
    return label + str(value)


def digit_count_positive(n: int) -> int:
    # Count digits by converting to string
    s: str = str(n)
    return len(s)


def main() -> None:
    # str(int) produces decimal representation
    assert int_to_str(42) == "42"
    assert int_to_str(0) == "0"
    assert int_to_str(-7) == "-7"

    # roundtrip: int(str(n)) == n
    assert roundtrip(42) == 42
    assert roundtrip(0) == 0
    assert roundtrip(-7) == -7

    # string concatenation with int conversion
    msg: str = str_concat_int("count: ", 5)
    assert msg == "count: 5"

    # len(str(n)) > 0 for any int
    assert digit_count_positive(0) == 1
    assert digit_count_positive(99) == 2
    assert digit_count_positive(100) == 3

    print(int_to_str(42), roundtrip(42), msg)


main()
