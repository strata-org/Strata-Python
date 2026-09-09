# Truth testing: supported case. Type is known, so truthiness is a pure
# predicate on the value.
"""Truth testing: supported case.
Type is known, so truthiness is a pure predicate on the value.
"""

def check_int(x: int) -> bool:
    return bool(x)  # True if x != 0

def check_list(lst: list) -> bool:
    return bool(lst)  # True if len > 0

def check_none(x: None) -> bool:
    return bool(x)  # always False

def filter_truthy(items: list[int]) -> list[int]:
    return [x for x in items if x]  # uses truth testing

if __name__ == "__main__":
    print(check_int(0))       # False
    print(check_int(42))      # True
    print(check_list([]))     # False
    print(check_list([1]))    # True
    print(check_none(None))   # False
    print(filter_truthy([0, 1, 0, 2, 0]))  # [1, 2]
