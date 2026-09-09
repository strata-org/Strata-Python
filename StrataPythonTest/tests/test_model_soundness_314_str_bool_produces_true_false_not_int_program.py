# `str(True)` → `"True"` not `"1"` — bool string conversion must dispatch on
# `from_bool` BEFORE `from_int`; normalization breaks it
"""
str(True) produces "True", not "1" — bool-specific string conversion.

In CPython, `str(True)` → `"True"` and `str(False)` → `"False"`.
This is DIFFERENT from `str(int(True))` → `"1"`. The bool type has
its own `__str__`/`__repr__` that produces the word, not the number.

The Laurel model's `to_str` (or `Any_to_str`) dispatch must handle
`from_bool` as a SEPARATE case from `from_int`. If the model normalizes
bool to int before string conversion (as finding 166 suggests for
arithmetic), it will produce "1"/"0" instead of "True"/"False".

This creates a tension:
- For ARITHMETIC: bool should normalize to int (True→1, False→0)
- For STRING CONVERSION: bool must NOT normalize (True→"True", False→"False")

The dispatch must be: check from_bool FIRST, produce "True"/"False";
only if from_int, produce the decimal string.

Similarly:
- str(None) → "None" (not some error or empty string)
- str(3.14) → "3.14" (specific float formatting)

Uses ONLY confirmed-accepted constructs: str(), bool, int, None, comparison.
"""


def bool_to_str_true() -> str:
    """str(True) must produce 'True' not '1'."""
    val: bool = True
    result: str = str(val)
    # CPython: "True"
    # Model (if bool normalized to int first): "1" — WRONG
    # Model (if to_str uninterpreted): Hole — unprovable
    return result


def bool_to_str_false() -> str:
    """str(False) must produce 'False' not '0'."""
    val: bool = False
    result: str = str(val)
    # CPython: "False"
    # Model (if bool normalized to int first): "0" — WRONG
    return result


def none_to_str() -> str:
    """str(None) must produce 'None'."""
    val: None = None
    result: str = str(val)
    # CPython: "None"
    # Model: likely Hole (no from_None case in to_str)
    return result


def bool_str_in_condition(flag: bool) -> str:
    """Use str(bool) result in string comparison."""
    s: str = str(flag)
    if s == "True":
        return "yes"
    return "no"


def bool_vs_int_str_divergence() -> bool:
    """Demonstrate that str(True) != str(1) even though True == 1."""
    # True == 1 is True (finding 294)
    # But str(True) != str(1)
    bool_str: str = str(True)   # "True"
    int_str: str = str(1)       # "1"
    # CPython: "True" != "1" → True (they differ)
    # Model: if bool normalized to int, both become "1" → False (WRONG)
    return bool_str != int_str


def str_in_fstring_context(x: int, flag: bool) -> str:
    """F-string uses str() implicitly; bool must produce 'True'/'False'."""
    # f"x={x}, flag={flag}" desugars to str(x) + ... + str(flag)
    # The str(flag) part must produce "True"/"False"
    result: str = "x=" + str(x) + ", flag=" + str(flag)
    # CPython: "x=5, flag=True"
    # Model: "x=5, flag=1" if bool normalized — WRONG
    return result


def comparison_result_to_str(a: int, b: int) -> str:
    """Comparison produces bool; str() of that bool must be 'True'/'False'."""
    is_greater: bool = a > b
    # is_greater is from_bool(True) or from_bool(False)
    result: str = str(is_greater)
    # CPython: "True" or "False"
    # Model: must dispatch on from_bool tag, not normalize to int
    return result


def main() -> None:
    assert bool_to_str_true() == "True"
    assert bool_to_str_false() == "False"
    assert none_to_str() == "None"

    assert bool_str_in_condition(True) == "yes"
    assert bool_str_in_condition(False) == "no"

    # Critical: str(True) != str(1)
    assert bool_vs_int_str_divergence() == True

    assert str_in_fstring_context(5, True) == "x=5, flag=True"
    assert str_in_fstring_context(3, False) == "x=3, flag=False"

    assert comparison_result_to_str(10, 5) == "True"
    assert comparison_result_to_str(3, 7) == "False"

    print("All str(bool) conversion tests pass")


main()
