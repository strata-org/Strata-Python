# String methods are pure (return new string, original unchanged) — model must
# not apply mutating-method patterns to str receivers
"""
String methods in Python return NEW strings (strings are immutable).
Unlike list.append() which mutates in place, str.upper()/lower()/strip()
etc. always return a new value. The original string is UNCHANGED.

The model's value semantics is actually CORRECT for strings (since
strings are immutable in CPython too). But the model might still get
this wrong if:
1. String methods are uninterpreted (return Hole) — finding 144/220
2. The model doesn't enforce that the ORIGINAL string is unchanged
3. The model conflates string method behavior with list method behavior

The critical test: after `result = s.upper()`, the original `s` must
still equal its original value. This is trivially true in CPython
(immutability) and should be trivially true in the model (value semantics).
But if the model has no axiom for string methods, it can't PROVE that
`s` is unchanged — it might think `s.upper()` could modify `s`.

This finding tests that the model correctly handles the interaction
between:
- String method calls (return new value)
- The original variable (must be provably unchanged)
- Chained operations (each produces a new string)

Uses ONLY confirmed-accepted constructs: str, method calls, comparison.
"""


def upper_preserves_original(s: str) -> bool:
    """Calling upper() doesn't change the original string."""
    original: str = s
    result: str = s.upper()
    # s must still equal original
    return s == original


def chained_methods_each_new(s: str) -> str:
    """Each method in a chain produces a new string."""
    step1: str = s.strip()
    step2: str = step1.lower()
    step3: str = step2.replace("a", "b")
    # s, step1, step2 are all unchanged by subsequent operations
    return step3


def method_on_parameter_no_mutation(text: str) -> str:
    """String parameter is not mutated by method calls."""
    cleaned: str = text.strip()
    lowered: str = cleaned.lower()
    return lowered


def caller_string_unchanged() -> bool:
    """Caller's string variable is unchanged after passing to function."""
    original: str = "  Hello World  "
    result: str = method_on_parameter_no_mutation(original)
    # original must still be "  Hello World  "
    return original == "  Hello World  "


def string_replace_returns_new(s: str, old: str, new: str) -> bool:
    """replace() returns new string; original unchanged."""
    result: str = s.replace(old, new)
    # Even if old is in s, s itself is unchanged
    # result may differ from s
    return s != result or old == new or len(s) == 0


def multiple_operations_independent() -> bool:
    """Multiple string operations on same source are independent."""
    base: str = "Hello"
    upper: str = base.upper()   # "HELLO"
    lower: str = base.lower()   # "hello"
    # base is still "Hello" — neither upper() nor lower() changed it
    # upper and lower are independent of each other
    return base == "Hello" and upper == "HELLO" and lower == "hello"


def main() -> None:
    # upper preserves original
    assert upper_preserves_original("hello") == True
    assert upper_preserves_original("ALREADY") == True
    assert upper_preserves_original("") == True

    # Chained methods
    assert chained_methods_each_new("  Hello  ") == "hello"
    assert chained_methods_each_new("  AAA  ") == "bbb"

    # Caller unchanged
    assert caller_string_unchanged() == True

    # Multiple operations independent
    assert multiple_operations_independent() == True

    print("All string immutability tests pass")


main()
