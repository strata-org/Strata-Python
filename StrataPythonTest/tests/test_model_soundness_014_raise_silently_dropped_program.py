# `raise` statement silently dropped (translated to empty); code after raise
# modeled as reachable
"""
The `raise` statement is silently dropped by the translator.
Code after a raise is modeled as reachable when it is not.
"""

def safe_divide(a: int, b: int) -> int:
    if b == 0:
        raise ValueError("division by zero")
    return a // b

def main() -> None:
    # CPython: raises ValueError, never reaches the print
    # Laurel: raise is dropped, execution falls through,
    #         safe_divide(10, 0) returns 10 // 0 which hits
    #         the PFloorDiv precondition (or returns garbage)
    result: int = safe_divide(10, 0)
    # CPython: unreachable
    # Laurel: reachable, result has some value
    print(result)

main()
