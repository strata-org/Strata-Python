# `and`/`or` return operand value not `from_bool` — `0 or 42` → `42` (int);
# model may wrap in from_bool, breaking downstream ops
"""
and/or RETURN OPERAND VALUE, NOT from_bool — TYPE TAG PRESERVED

CPython: 3 or 5 → 3 (int, not True!)
         0 or 5 → 5 (int, not True!)
         "" or "default" → "default" (str!)
         [1] and [2] → [2] (list!)

         Python's `and`/`or` return ONE OF THEIR OPERANDS, not a boolean.
         The return type is the type of the selected operand.

Model:   Finding 056 identified this issue. But the specific TAG interaction
         is: if the model wraps the result in from_bool(), downstream
         operations expecting the original type FAIL.

         Example: x = value or default
         If value is from_int(0): result should be from_int(default)
         If model returns from_bool(True/False): downstream int ops fail.

This is critical for the "default value" pattern:
    port = config.get("port") or 8080
    name = user_name or "anonymous"
"""


def first_truthy_int(a: int, b: int) -> int:
    """or returns first truthy operand (preserving int type)."""
    return a or b


def both_true_int(a: int, b: int) -> int:
    """and returns last operand if all truthy (preserving int type)."""
    return a and b


def default_string(s: str, default: str) -> str:
    """Common pattern: use default if string is empty."""
    return s or default


def guard_and_use(x: int, threshold: int) -> int:
    """and short-circuits: if x is 0, returns 0 (int), not False."""
    return x and x + threshold


def chained_or(a: int, b: int, c: int) -> int:
    """Chained or: returns first truthy value."""
    return a or b or c


def main() -> None:
    # Test 1: or returns the VALUE, not True/False
    result: int = first_truthy_int(0, 42)
    # CPython: 42 (int)
    # Model: if or returns from_bool(True) → wrong tag, downstream int ops fail
    assert result == 42
    assert isinstance(result, int)

    # Test 2: or returns first truthy
    assert first_truthy_int(7, 42) == 7  # 7 is truthy, returned directly

    # Test 3: and returns last if all truthy
    result2: int = both_true_int(3, 5)
    # CPython: 5 (int, the last truthy operand)
    # Model: if and returns from_bool(True) → wrong tag
    assert result2 == 5

    # Test 4: and returns first falsy
    assert both_true_int(0, 5) == 0  # 0 is falsy, returned directly

    # Test 5: string default pattern
    assert default_string("hello", "world") == "hello"
    assert default_string("", "world") == "world"

    # Test 6: guard pattern
    assert guard_and_use(5, 10) == 15  # 5 is truthy → 5 + 10
    assert guard_and_use(0, 10) == 0   # 0 is falsy → returns 0 (not False!)

    # Test 7: chained
    assert chained_or(0, 0, 99) == 99
    assert chained_or(0, 7, 99) == 7

    print("all passed")


main()
