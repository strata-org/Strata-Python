# Exception-as-value has no stack unwinding — must insert explicit propagation
# checks after every raising operation; without them handlers unreachable
"""
CPython uses stack unwinding for exceptions: when raised, execution
jumps to the nearest enclosing except handler. No intermediate code runs.

The Laurel model uses exception VALUES: `exception(...)` is a tag in the
Any union. There is NO jump. Code continues executing sequentially.

This means the translator must INSERT explicit checks after every
operation that might produce an exception. Without these checks,
exception values flow silently into subsequent operations.

Finding 173 identified this. This finding shows the MINIMAL translation
pattern required to make exception-as-value behave like stack unwinding.

Uses ONLY confirmed-accepted constructs: try/except, int, function def.
"""


def simple_try_except() -> int:
    """Basic: operation raises, handler catches."""
    try:
        x: int = 10 // 0  # raises ZeroDivisionError
        y: int = x + 1    # must NOT execute
        return y           # must NOT execute
    except ZeroDivisionError:
        return -1


def multiple_statements_after_raise() -> int:
    """All statements after the raising operation are skipped."""
    try:
        a: int = 5
        b: int = 0
        c: int = a // b   # raises here
        d: int = c * 2    # skipped
        e: int = d + 10   # skipped
        return e           # skipped
    except ZeroDivisionError:
        return 99


def raise_in_middle() -> int:
    """Statements before raise execute; after don't."""
    result: int = 0
    try:
        result = result + 1   # executes: result = 1
        result = result + 1   # executes: result = 2
        x: int = 1 // 0      # raises
        result = result + 1   # skipped
        result = result + 1   # skipped
    except ZeroDivisionError:
        pass
    return result  # 2 (only first two additions ran)


def nested_function_raise() -> int:
    """Exception in called function propagates to caller's handler."""
    def divide(a: int, b: int) -> int:
        return a // b  # may raise

    try:
        x: int = divide(10, 0)  # raises inside divide
        y: int = x + 1          # skipped
        return y                 # skipped
    except ZeroDivisionError:
        return -1


def main() -> None:
    assert simple_try_except() == -1
    assert multiple_statements_after_raise() == 99
    assert raise_in_middle() == 2
    assert nested_function_raise() == -1

    print(simple_try_except(), multiple_statements_after_raise(),
          raise_in_middle())


main()
