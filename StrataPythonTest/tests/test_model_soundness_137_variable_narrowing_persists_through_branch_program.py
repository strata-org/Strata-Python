# Variable narrowing must persist through entire branch — `assume` after `is
# not None` must remain in scope for all subsequent code
"""
After `if isinstance(x, int):`, the variable `x` is narrowed to `int`
for the ENTIRE true branch — including nested ifs, function calls, and
assignments. The narrowing must persist until the branch ends or `x` is
reassigned.

If the model only narrows at the immediate next statement (not the
whole branch), subsequent uses of `x` lose the narrowing.
"""
from typing import Optional


def process_optional(x: Optional[int]) -> int:
    if x is not None:
        # x is narrowed to int for this ENTIRE branch
        doubled: int = x * 2
        incremented: int = doubled + 1
        if incremented > 10:
            return incremented  # x still known to be int here
        return x + 100  # x still narrowed here too
    return -1


def multi_statement_after_narrow(x: Optional[str]) -> str:
    if x is None:
        return "empty"
    # x is narrowed to str for ALL remaining code in this function
    upper: str = x  # x is str
    result: str = upper + "!"
    if len(result) > 5:
        return result  # x still str
    return x + "?"  # x still str


def nested_narrowing(x: Optional[int], y: Optional[int]) -> int:
    if x is not None:
        if y is not None:
            # Both narrowed
            return x + y
        return x
    if y is not None:
        return y
    return 0


def main() -> None:
    # Optional narrowing persists through branch
    assert process_optional(10) == 21   # 10*2+1=21 > 10
    assert process_optional(4) == 104   # 4*2+1=9 <= 10, return 4+100
    assert process_optional(None) == -1

    # Multi-statement after narrowing
    assert multi_statement_after_narrow(None) == "empty"
    assert multi_statement_after_narrow("hi") == "hi?"
    assert multi_statement_after_narrow("hello world") == "hello world!"

    # Nested narrowing
    assert nested_narrowing(3, 4) == 7
    assert nested_narrowing(3, None) == 3
    assert nested_narrowing(None, 4) == 4
    assert nested_narrowing(None, None) == 0

    print(process_optional(4), multi_statement_after_narrow("hi"))


main()
