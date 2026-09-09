# String concatenation length axioms — `len(s + t) == len(s) + len(t)`
# unprovable if `str_concat` is uninterpreted (not mapped to SMT-LIB `str.++`)
"""
Python's string concatenation with `+` requires both operands to be str.
`str + int` raises TypeError. But `str(x) + str(y)` is the standard
pattern for building strings from mixed types.

The issue: if `PAdd(from_str(s), from_str(t))` uses `str_concat` but
the SMT string theory's concat has no length axioms, then
`len(s + t) == len(s) + len(t)` is unprovable. Similarly,
`s + "" == s` (identity) and `(s + t) + u == s + (t + u)` (associativity)
may be unprovable if str_concat is uninterpreted.
"""


def repeat_join(s: str, n: int) -> str:
    result: str = ""
    i: int = 0
    while i < n:
        result = result + s
        i = i + 1
    return result


def build_csv(values: list[int]) -> str:
    if len(values) == 0:
        return ""
    result: str = str(values[0])
    i: int = 1
    while i < len(values):
        result = result + "," + str(values[i])
        i = i + 1
    return result


def pad_right(s: str, width: int) -> str:
    padding: str = ""
    i: int = len(s)
    while i < width:
        padding = padding + " "
        i = i + 1
    return s + padding


def main() -> None:
    # String concat length property
    a: str = "hello"
    b: str = " world"
    c: str = a + b
    assert len(c) == 11  # len("hello") + len(" world")

    # Identity: s + "" == s
    assert a + "" == a

    # repeat_join builds by accumulation
    r: str = repeat_join("ab", 3)
    assert r == "ababab"
    assert len(r) == 6

    # build_csv
    csv: str = build_csv([1, 2, 3])
    # Depends on str(int) having a model (finding 053)

    # pad_right
    p: str = pad_right("hi", 5)
    assert len(p) == 5

    print(c, r, p)


main()
