# F-strings reduce to str() + concatenation — `f"{x}"` needs int_to_str model
# (finding 053) + desugar to concat chain
"""
F-strings (`f"x={x}"`) are IN the subset (finding 083 noted no model).
But the subset also says string methods like format are OUT.

The key issue: f-strings require implicit str() conversion of embedded
expressions. `f"{x}"` where x is int calls `str(x)` implicitly.

Finding 053 identified str(int) has no axioms. Finding 083 identified
f-strings have no model. This finding shows that f-strings are
REDUCIBLE to str() + concatenation — both of which need models.

Uses ONLY confirmed-accepted constructs: f-string, int, str.
"""


def simple_fstring(name: str) -> str:
    return f"hello {name}"


def int_in_fstring(x: int) -> str:
    return f"value={x}"


def multiple_expressions(a: int, b: int) -> str:
    return f"{a} + {b} = {a + b}"


def fstring_with_method(s: str) -> str:
    return f"upper: {s.upper()}"


def conditional_fstring(x: int) -> str:
    label: str = "positive" if x > 0 else "non-positive"
    return f"{x} is {label}"


def fstring_in_loop(xs: list[int]) -> str:
    result: str = ""
    for x in xs:
        result = result + f"{x},"
    return result


def main() -> None:
    assert simple_fstring("world") == "hello world"
    assert int_in_fstring(42) == "value=42"
    assert multiple_expressions(3, 4) == "3 + 4 = 7"
    assert fstring_with_method("hello") == "upper: HELLO"
    assert conditional_fstring(5) == "5 is positive"
    assert conditional_fstring(-1) == "-1 is non-positive"
    assert fstring_in_loop([1, 2, 3]) == "1,2,3,"

    print(simple_fstring("world"), int_in_fstring(42),
          multiple_expressions(3, 4))


main()
