# String equality after concat unprovable — `"a"+"b" == "ab"` needs str_concat
# mapped to SMT-LIB `str.++`; uninterpreted = unknown
"""
CPython: "hello" + " " + "world" == "hello world" → True
Model: str_concat is uninterpreted → PEq(str_concat(str_concat("hello"," "),"world"), "hello world") → UNKNOWN

The model CANNOT PROVE this equality because str_concat has no axioms
connecting it to string literals. The solver sees two opaque terms and
can't determine they're equal.

CPython result: True (assertion passes)
Model result: UNKNOWN/unprovable (verifier says "cannot verify")

This is a FALSE NEGATIVE: the model rejects a correct program.
"""


def concat_equals_literal() -> bool:
    """Concatenation result must equal the expected literal."""
    result: str = "hello" + " " + "world"
    return result == "hello world"  # True in CPython, unprovable in model


def build_and_compare() -> bool:
    """Build string piece by piece, compare to expected."""
    prefix: str = "key"
    sep: str = "="
    value: str = "42"
    full: str = prefix + sep + value
    return full == "key=42"  # True in CPython, unprovable in model


def empty_concat_identity() -> bool:
    """Concatenating empty string is identity."""
    s: str = "test"
    result: str = "" + s + ""
    return result == s  # True in CPython, unprovable without axiom


def concat_associativity() -> bool:
    """(a + b) + c == a + (b + c) — must hold."""
    a: str = "ab"
    b: str = "cd"
    c: str = "ef"
    left: str = (a + b) + c
    right: str = a + (b + c)
    return left == right  # True in CPython, unprovable without axiom


def main() -> None:
    assert concat_equals_literal() == True
    assert build_and_compare() == True
    assert empty_concat_identity() == True
    assert concat_associativity() == True

    print(concat_equals_literal(), build_and_compare(),
          empty_concat_identity())


main()
