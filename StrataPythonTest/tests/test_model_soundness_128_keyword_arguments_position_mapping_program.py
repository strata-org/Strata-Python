# Keyword arguments — `f(y=2, x=1)` must map by name to position; if
# translator uses call-site order, args are swapped
"""
Keyword arguments (`f(y=2, x=1)`) pass arguments by name, not position.
The translator must map keyword args to the correct parameter positions.
If it only handles positional args, keyword calls produce wrong bindings.
"""


def divide(numerator: int, denominator: int) -> int:
    return numerator // denominator


def create_range(start: int, stop: int, step: int) -> list[int]:
    result: list[int] = []
    i: int = start
    while i < stop:
        result = result + [i]
        i = i + step
    return result


def format_name(first: str, last: str, title: str) -> str:
    return title + " " + first + " " + last


def main() -> None:
    # Positional: order matters
    assert divide(10, 3) == 3

    # Keyword: names matter, order doesn't
    assert divide(numerator=10, denominator=3) == 3
    assert divide(denominator=3, numerator=10) == 3  # reversed order!

    # Mixed: positional first, then keyword
    assert divide(10, denominator=3) == 3

    # If translator ignores keywords and uses position:
    # divide(denominator=3, numerator=10) → divide(3, 10) = 0 (WRONG)

    # Range with keyword args
    r: list[int] = create_range(stop=10, start=0, step=2)
    assert r == [0, 2, 4, 6, 8]

    # Format name with keywords
    name: str = format_name(last="Smith", first="John", title="Dr.")
    assert name == "Dr. John Smith"

    print(divide(denominator=3, numerator=10), name)


main()
