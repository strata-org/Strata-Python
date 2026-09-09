# try/except inside loop — per-iteration exception scope; catching in one
# iteration must not exit the entire loop
"""
try/except inside a loop. Each iteration may raise, and the handler
allows the loop to continue. The exception is caught PER ITERATION,
not once for the whole loop.

All constructs used: while, try/except, int, ValueError — all IN.
Frontend accepts this.
"""


def parse_numbers(strings: list[str]) -> list[int]:
    """Parse each string to int; skip invalid ones."""
    result: list[int] = []
    for s in strings:
        try:
            n: int = int(s)
            result.append(n)
        except ValueError:
            pass  # skip invalid
    return result


def safe_divide_all(xs: list[int], divisor: int) -> list[int]:
    """Divide each element; use 0 on ZeroDivisionError."""
    result: list[int] = []
    for x in xs:
        try:
            result.append(x // divisor)
        except ZeroDivisionError:
            result.append(0)
    return result


def count_valid(strings: list[str]) -> int:
    """Count how many strings are valid integers."""
    count: int = 0
    for s in strings:
        try:
            n: int = int(s)
            count = count + 1
        except ValueError:
            pass
    return count


def first_valid(strings: list[str]) -> int:
    """Return first valid integer, or -1."""
    for s in strings:
        try:
            return int(s)
        except ValueError:
            pass
    return -1


def main() -> None:
    assert parse_numbers(["1", "bad", "3", "x", "5"]) == [1, 3, 5]
    assert parse_numbers([]) == []
    assert parse_numbers(["bad"]) == []

    assert safe_divide_all([10, 20, 30], 5) == [2, 4, 6]
    assert safe_divide_all([10, 20, 30], 0) == [0, 0, 0]

    assert count_valid(["1", "x", "3"]) == 2
    assert count_valid(["x", "y"]) == 0

    assert first_valid(["bad", "3", "5"]) == 3
    assert first_valid(["x", "y"]) == -1

    print(parse_numbers(["1", "x", "3"]), count_valid(["1", "x", "3"]),
          first_valid(["bad", "5"]))


main()
