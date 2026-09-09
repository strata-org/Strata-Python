# F-string interpolation (`f"x={x}"`) has no model — requires `str()`
# conversion (finding 053) + multi-part concatenation
"""
F-strings (`f"x={x}"`) desugar to a series of str() conversions and
string concatenations. The model needs:
1. str(int) → from_str (finding 053 notes no axioms)
2. str(float) → from_str
3. str(bool) → from_str("True"/"False")
4. Concatenation of the literal parts with the converted expressions

If the translator doesn't desugar f-strings, or if str() conversions
have no model, the result is Hole.
"""


def greet(name: str, age: int) -> str:
    return f"Hello, {name}! You are {age} years old."


def format_point(x: int, y: int) -> str:
    return f"({x}, {y})"


def status_message(count: int, total: int) -> str:
    return f"Processed {count} of {total} items"


def bool_label(flag: bool) -> str:
    return f"enabled={flag}"


def multi_expr(a: int, b: int) -> str:
    return f"{a} + {b} = {a + b}"


def main() -> None:
    # Basic f-string with string and int
    msg: str = greet("Alice", 30)
    assert msg == "Hello, Alice! You are 30 years old."

    # F-string with multiple ints
    pt: str = format_point(3, 4)
    assert pt == "(3, 4)"

    # F-string with expression
    expr: str = multi_expr(2, 3)
    assert expr == "2 + 3 = 5"

    # F-string with bool
    lbl: str = bool_label(True)
    assert lbl == "enabled=True"

    # Status
    st: str = status_message(7, 10)
    assert st == "Processed 7 of 10 items"

    print(msg)
    print(pt)
    print(expr)


main()
