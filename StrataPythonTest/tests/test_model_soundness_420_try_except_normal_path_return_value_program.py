# Try/except normal path — `try: n=int("42")` on success must flow n=42 to
# post-try scope; model may lose the value or give Hole
"""
TRY/EXCEPT NORMAL PATH RETURN VALUE — MUST FLOW THROUGH

CPython: try: n = int("42") except ValueError: n = -1
         → n == 42 (no exception, normal path)

Model:   Even on the NORMAL path (no exception), the model may fail:
         - int("42") returns Hole (finding 017) → n is Hole
         - try block translation may not connect normal-path value to post-try variable
         - The variable `n` after try/except must hold the try-block value
           when no exception occurred

         This is different from finding 406 (handler unreachable).
         This tests the NORMAL PATH: no exception raised, value flows through.

CPython result: n == 42
Model result: Hole (int() has no model) or unconstrained (try block doesn't connect)

Root cause: int() returns Hole (finding 017), AND try-block normal-path
variable flow may not be connected to post-try scope.
"""


def parse_safe(s: str) -> int:
    """Normal path: int succeeds, value flows through try."""
    try:
        n: int = int(s)
    except ValueError:
        n = -1
    return n


def divide_safe(a: int, b: int) -> int:
    """Normal path: division succeeds."""
    try:
        result: int = a // b
    except ZeroDivisionError:
        result = 0
    return result


def access_safe(xs: list[int], i: int) -> int:
    """Normal path: index access succeeds."""
    try:
        val: int = xs[i]
    except IndexError:
        val = -1
    return val


def try_with_computation(x: int) -> int:
    """Computation in try block — result must flow to post-try."""
    try:
        a: int = x * 2
        b: int = a + 1
        result: int = b
    except ValueError:
        result = 0
    return result


def main() -> None:
    # Test 1: normal path — int succeeds
    assert parse_safe("42") == 42
    assert parse_safe("0") == 0

    # Test 2: exception path — handler executes
    assert parse_safe("abc") == -1

    # Test 3: division normal path
    assert divide_safe(10, 3) == 3

    # Test 4: division exception path
    assert divide_safe(10, 0) == 0

    # Test 5: index normal path
    assert access_safe([10, 20, 30], 1) == 20

    # Test 6: index exception path
    assert access_safe([10, 20, 30], 10) == -1

    # Test 7: computation in try
    assert try_with_computation(5) == 11  # 5*2+1

    print("all passed")


main()
