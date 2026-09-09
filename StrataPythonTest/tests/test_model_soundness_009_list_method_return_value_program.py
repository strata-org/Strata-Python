# list.append() has no model; havoc fallback loses return-value (always None)
# and list-growth semantics
"""
list.append() returns None in CPython but the Laurel encoding
havocs the receiver variable to an arbitrary ListAny value.
A program that branches on the return value of append diverges.
"""

def process(xs: list[int], val: int) -> int:
    result = xs.append(val)
    # CPython: result is None, so this is always False
    if result is not None:
        return -1
    return len(xs)

def main() -> None:
    nums: list[int] = [1, 2, 3]
    out: int = process(nums, 4)
    # CPython: out == 4 (len after append)
    # Laurel: xs is havoc'd, result is Hole (unconstrained Any),
    #         the `is not None` branch is feasible → may return -1
    print(out)

main()
