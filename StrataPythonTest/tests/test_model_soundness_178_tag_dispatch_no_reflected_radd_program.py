# Tag dispatch no reflected methods — `int * str` needs `PMul(from_int,
# from_str)` case; model only has left-primary dispatch
"""
Python's operator dispatch uses a two-step protocol:
1. Try left operand's __add__ (or __lt__, etc.)
2. If it returns NotImplemented, try right operand's __radd__

The Laurel model dispatches by pattern matching on the LEFT tag only.
There is no reflected method fallback.

In the Frontend subset, user-defined __add__/__radd__ are OUT. But the
BUILT-IN reflected dispatch still matters:

- `int * str`: int.__mul__(str) returns NotImplemented,
  then str.__rmul__(int) is called → works
- `int + float`: int.__add__(float) returns NotImplemented,
  then float.__radd__(int) is called → works (with promotion)

Finding 035 identified `int * str`. Finding 024 identified `int + float`.
This finding shows the SYSTEMATIC issue: the model's tag dispatch has
the LEFT operand as primary, but Python tries BOTH sides.

For built-in types, this means the model needs BOTH orderings:
  PMul(from_int, from_str) AND PMul(from_str, from_int)

Uses ONLY confirmed-accepted constructs: int, str, float, *, +.
"""


def int_times_str(n: int, s: str) -> str:
    """int * str — requires reflected dispatch (str.__rmul__)."""
    return n * s


def str_times_int(s: str, n: int) -> str:
    """str * int — direct dispatch (str.__mul__)."""
    return s * n


def int_plus_float(a: int, b: float) -> float:
    """int + float — requires promotion or reflected dispatch."""
    return a + b


def float_plus_int(a: float, b: int) -> float:
    """float + int — direct dispatch."""
    return a + b


def int_minus_float(a: int, b: float) -> float:
    return a - b


def int_div_float(a: int, b: float) -> float:
    return a / b


def symmetry_check() -> bool:
    """Both orderings must produce the same result."""
    # int * str vs str * int
    assert 3 * "ab" == "ab" * 3
    # int + float vs float + int
    assert 2 + 3.5 == 3.5 + 2
    # int - float (only one ordering makes sense semantically)
    assert 10 - 2.5 == 7.5
    return True


def main() -> None:
    # int * str (reflected)
    assert int_times_str(3, "ab") == "ababab"
    assert int_times_str(0, "hello") == ""
    assert int_times_str(1, "x") == "x"

    # str * int (direct)
    assert str_times_int("ab", 3) == "ababab"

    # int + float (reflected/promoted)
    assert int_plus_float(2, 3.5) == 5.5
    assert float_plus_int(3.5, 2) == 5.5

    # int - float
    assert int_minus_float(10, 2.5) == 7.5

    # int / float
    assert int_div_float(10, 4.0) == 2.5

    # Symmetry
    assert symmetry_check() == True

    print(int_times_str(3, "ab"), int_plus_float(2, 3.5),
          int_minus_float(10, 2.5))


main()
