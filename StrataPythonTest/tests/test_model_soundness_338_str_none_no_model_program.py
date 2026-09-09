# `str(None)` → `"None"` has no model — str conversion function has no
# `from_None` case; returns Hole for trivial constant
"""
str() CONVERSION ON None PRODUCES "None" — NO MODEL

CPython: str(None) → "None" (the string literal)
Model:   str_from_any(from_None()) → Hole (no case for None tag)

The subset declares str(x) as IN for "primitive-type conversions."
None is a primitive value in the subset. But the model's str conversion
function likely only handles from_int, from_float, from_bool, from_str
and has no case for from_None.
"""


def format_value(x: int, label: str) -> str:
    return label + ": " + str(x)


def format_optional(x: int, suffix: str) -> str:
    # str() on None is needed when building messages about optional values
    # Even without Optional[int], str(None) can appear in subset code
    return str(x) + suffix


def none_to_str() -> str:
    # Direct conversion
    result: str = str(None)
    # CPython: "None"
    # Model: Hole (no from_None case in str conversion)
    return result


def bool_to_str() -> str:
    # For comparison: bool conversion
    result: str = str(True)
    # CPython: "True"
    # Model: may return "True" if from_bool case exists, or Hole
    return result


def int_to_str() -> str:
    result: str = str(42)
    # CPython: "42"
    # Model: Hole (finding 053 — no int-to-str axioms)
    return result


def build_debug_message(name: str, value: int, found: bool) -> str:
    # Common pattern: building debug/log strings with mixed types
    parts: list[str] = []
    parts.append("name=" + name)
    parts.append("value=" + str(value))
    parts.append("found=" + str(found))
    return ", ".join(parts)


def main() -> None:
    # Test 1: str(None) == "None"
    s: str = none_to_str()
    assert s == "None"

    # Test 2: str(True) == "True" (not "1")
    # Related to finding 314 but here we test the str() builtin call
    assert bool_to_str() == "True"

    # Test 3: str(False) == "False"
    assert str(False) == "False"

    # Test 4: length of str(None)
    assert len(str(None)) == 4

    # Test 5: str(None) in condition
    if str(None) == "None":
        result: str = "correct"
    else:
        result = "wrong"
    assert result == "correct"

    print(s)


main()
