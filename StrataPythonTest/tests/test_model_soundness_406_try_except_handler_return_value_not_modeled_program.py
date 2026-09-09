# Try/except handler unreachable — `int("abc")` returns Hole not exception;
# handler never executes; `safe_parse` returns Hole not -1
"""
TRY/EXCEPT HANDLER RETURN VALUE — MODEL DOESN'T REACH HANDLER

CPython: def safe_parse(s: str) -> int:
             try:
                 return int(s)
             except ValueError:
                 return -1
         safe_parse("abc") → -1 (handler returns -1)

Model:   int(s) either:
         - Returns Hole (no model for int(), finding 017)
         - Returns from_int(some_value) (no exception produced)
         The except handler is UNREACHABLE in the model because
         int() never produces an exception value.

         Even if int() DID produce exception(ValueError):
         - Finding 274: no propagation to handler
         - Finding 113: handler may not match exception type
         - Finding 206: no stack unwinding

         Result: safe_parse("abc") returns Hole (from int()),
         not -1 (from handler). The handler code is dead.
"""


def safe_parse(s: str) -> int:
    """The subset's own exception example pattern."""
    try:
        n: int = int(s)
    except ValueError:
        return -1
    return n


def safe_divide(a: int, b: int) -> int:
    """Division with exception handling."""
    try:
        return a // b
    except ZeroDivisionError:
        return 0


def safe_index(xs: list[int], i: int) -> int:
    """List access with exception handling."""
    try:
        return xs[i]
    except IndexError:
        return -1


def parse_or_default(s: str, default: int) -> int:
    """Parse with custom default."""
    try:
        result: int = int(s)
    except ValueError:
        result = default
    return result


def main() -> None:
    # Test 1: safe_parse with valid input
    assert safe_parse("42") == 42

    # Test 2: safe_parse with INVALID input — handler must execute
    # CPython: int("abc") raises ValueError → handler returns -1
    # Model: int("abc") returns Hole → handler unreachable → returns Hole
    assert safe_parse("abc") == -1

    # Test 3: safe_divide
    assert safe_divide(10, 3) == 3
    assert safe_divide(10, 0) == 0  # handler returns 0

    # Test 4: safe_index
    assert safe_index([1, 2, 3], 1) == 2
    assert safe_index([1, 2, 3], 10) == -1  # handler returns -1

    # Test 5: parse_or_default
    assert parse_or_default("5", 0) == 5
    assert parse_or_default("xyz", 99) == 99

    print("all passed")


main()
