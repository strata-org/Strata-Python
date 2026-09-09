# List_contains uses structural equality; misses bool/int equivalence (True !=
# from_int(1) structurally)
"""
Python's `in` operator uses == for comparison, and bool is a subtype of int
(True == 1, False == 0). List_contains in Laurel uses structural equality
on the Any datatype, so from_bool(true) != from_int(1) structurally.
"""

def has_one(xs: list[int]) -> bool:
    return 1 in xs

def main() -> None:
    flags: list[int] = [0, 1, 2]
    # This works fine — int in list[int]
    print(has_one(flags))  # True

    # But bool/int equivalence breaks:
    values: list[int] = [0, 1, 2]
    found: bool = True in values
    # CPython: True (because True == 1 and 1 is in the list)
    # Laurel: False (List_contains checks from_bool(true) == from_int(1)
    #         which is structural inequality — different constructors)
    print(found)

    # Reverse direction also breaks:
    bools: list[bool] = [True, False]
    found2: bool = 1 in bools
    # CPython: True (because 1 == True)
    # Laurel: False (from_int(1) != from_bool(true) structurally)
    print(found2)

main()
