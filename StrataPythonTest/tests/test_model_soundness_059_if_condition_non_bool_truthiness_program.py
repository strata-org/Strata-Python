# `if`/`while` condition with non-bool expression — truthiness coercion
# (`Any_to_bool`) not inserted in condition position
"""
Python's `if` statement evaluates truthiness of the condition expression.
`if n:` is equivalent to `if bool(n):`. For int, 0 is falsy; for str,
"" is falsy; for list, [] is falsy. If the model only accepts `from_bool`
in condition position, non-bool conditions produce wrong control flow
or Hole.
"""


def sign(n: int) -> str:
    if n:
        if n > 0:
            return "positive"
        return "negative"
    return "zero"


def first_or_default(xs: list[int], default: int) -> int:
    if xs:
        return xs[0]
    return default


def label_or_unnamed(name: str) -> str:
    if name:
        return name
    return "unnamed"


def main() -> None:
    # int truthiness in condition
    assert sign(5) == "positive"
    assert sign(-3) == "negative"
    assert sign(0) == "zero"

    # list truthiness in condition
    assert first_or_default([10, 20], -1) == 10
    assert first_or_default([], -1) == -1

    # str truthiness in condition
    assert label_or_unnamed("Alice") == "Alice"
    assert label_or_unnamed("") == "unnamed"

    print(sign(5), first_or_default([], -1), label_or_unnamed(""))


main()
