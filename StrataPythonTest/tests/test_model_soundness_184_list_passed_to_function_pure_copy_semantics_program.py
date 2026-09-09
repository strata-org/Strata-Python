# List passed to function — pure copy semantics diverges from CPython if
# caller doesn't capture return; AST check must enforce
"""
When a list is passed to a function, the function receives a COPY under
pure/value semantics. This is CORRECT for the Frontend subset (no aliasing
rule). But the function's RETURN value must be the mechanism for
communicating list changes back to the caller.

The pattern:
    def process(xs: list[int]) -> list[int]:
        xs.append(99)
        return xs

    data = [1, 2, 3]
    data = process(data)  # caller must rebind!

Under value semantics, `process` gets a copy. Its append modifies the
copy. The caller only sees changes if it captures the return value.

This finding verifies that the CORRECT pattern (return modified list)
works, and documents that the INCORRECT pattern (modify param, don't
return) is correctly rejected by value semantics.

Uses ONLY confirmed-accepted constructs: list, function, int.
"""


def append_and_return(xs: list[int], val: int) -> list[int]:
    """Correct pattern: modify and return."""
    xs.append(val)
    return xs


def filter_positive(xs: list[int]) -> list[int]:
    """Build new list from input — pure function."""
    result: list[int] = []
    for x in xs:
        if x > 0:
            result.append(x)
    return result


def transform_elements(xs: list[int]) -> list[int]:
    """Return new list with transformed elements."""
    result: list[int] = []
    for x in xs:
        result.append(x * 2)
    return result


def take_first_n(xs: list[int], n: int) -> list[int]:
    """Return first n elements."""
    result: list[int] = []
    i: int = 0
    while i < n and i < len(xs):
        result.append(xs[i])
        i = i + 1
    return result


def caller_rebinds() -> list[int]:
    """Caller captures return value — sees the modification."""
    data: list[int] = [1, 2, 3]
    data = append_and_return(data, 4)
    # data is now [1, 2, 3, 4] because we rebound
    return data


def caller_forgets() -> list[int]:
    """Caller doesn't capture return — modification lost (value semantics)."""
    data: list[int] = [1, 2, 3]
    append_and_return(data, 4)  # return value discarded!
    # Under value semantics: data is still [1, 2, 3]
    # Under CPython reference semantics: data is [1, 2, 3, 4]
    # THIS IS WHERE THE MODEL DIVERGES FROM CPYTHON
    return data


def main() -> None:
    # Correct pattern: rebind
    assert caller_rebinds() == [1, 2, 3, 4]

    # Incorrect pattern: forget to rebind
    # CPython: data is [1, 2, 3, 4] (mutation visible)
    # Model: data is [1, 2, 3] (copy semantics)
    result: list[int] = caller_forgets()
    # In CPython this is [1, 2, 3, 4] — the model says [1, 2, 3]
    # The SUBSET RULE says this pattern is OUT (no aliasing)
    # But if it slips through, the model is wrong

    # Pure functions work correctly
    assert filter_positive([-1, 2, -3, 4]) == [2, 4]
    assert transform_elements([1, 2, 3]) == [2, 4, 6]
    assert take_first_n([10, 20, 30, 40], 2) == [10, 20]

    print(caller_rebinds(), filter_positive([-1, 2, -3, 4]),
          take_first_n([10, 20, 30], 2))


main()
