# Comparison: supported case. Types are known, so richcompare dispatch
# collapses to native predicates.
"""Comparison: supported case.
Types are known, so richcompare dispatch collapses to native predicates.
"""

def compare_ints(x: int, y: int) -> tuple[bool, bool, bool]:
    return (x == y, x < y, x >= y)

def compare_strs(a: str, b: str) -> bool:
    return a == b

def cross_type(x: int, y: str) -> bool:
    return x == y  # always False for int vs str

if __name__ == "__main__":
    print(compare_ints(3, 5))    # (False, True, False)
    print(compare_strs("a", "a"))  # True
    print(cross_type(1, "1"))    # False
