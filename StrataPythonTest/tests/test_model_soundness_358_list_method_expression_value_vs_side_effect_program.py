# List method expression value vs side effect — `x = lst.append(v)` gives
# x=None; model may give x=new_list if conflating return with side effect
"""
LIST METHOD EXPRESSION VALUE VS SIDE EFFECT — USING RETURN VALUE OF APPEND

CPython: x = lst.append(5) → x is None (append returns None)
         lst.sort() → returns None (sort is in-place)
         lst.reverse() → returns None

         If someone writes: new_list = old_list.append(5)
         They get None, not the extended list!

Model:   If translator models append as pure function returning new list:
         new_list = List_append(old_list, 5) → new_list is the extended list
         This is WRONG — the expression value should be from_None().

         The model must distinguish:
         1. The SIDE EFFECT: old_list gets a new element (rebind)
         2. The EXPRESSION VALUE: from_None() (what .append() returns)

         If the translator conflates these, code that uses the return value
         of append/sort/reverse gets a list instead of None.
"""


def append_return_value() -> bool:
    """append() returns None, not the list."""
    xs: list[int] = [1, 2, 3]
    result: object = xs.append(4)
    # CPython: result is None
    # Model: if append modeled as pure function, result might be [1,2,3,4]
    return result is None


def sort_return_value() -> bool:
    """sort() returns None, not the sorted list."""
    xs: list[int] = [3, 1, 2]
    result: object = xs.sort()
    # CPython: result is None, xs is [1, 2, 3]
    return result is None


def chain_mistake() -> int:
    """Common bug: trying to chain append."""
    xs: list[int] = [1, 2]
    # This is a BUG in user code — append returns None
    # The verifier should catch this as a type error
    ys: list[int] = []
    ys.append(10)
    ys.append(20)
    # Correct usage: ys is now [10, 20]
    return len(ys)


def build_correctly() -> list[int]:
    """Correct pattern: ignore return value, use the list."""
    result: list[int] = []
    result.append(1)
    result.append(2)
    result.append(3)
    # result is [1, 2, 3] — the list was mutated
    return result


def main() -> None:
    # Test 1: append returns None
    assert append_return_value()

    # Test 2: sort returns None
    assert sort_return_value()

    # Test 3: correct usage
    assert chain_mistake() == 2

    # Test 4: build correctly
    built: list[int] = build_correctly()
    assert built == [1, 2, 3]

    print("all passed")


main()
