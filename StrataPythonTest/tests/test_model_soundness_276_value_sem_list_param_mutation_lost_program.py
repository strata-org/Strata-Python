# Value sem: list param mutation lost — `f(lst); lst.append(x)` inside f
# invisible to caller; CPython=[1,2,3,99], Model=[1,2,3]
"""
VALUE SEMANTICS WHERE CPYTHON HAS REFERENCE SEMANTICS:
List passed to function — function appends, caller sees change in CPython.

CPython: list param is a reference. append mutates the SAME object.
Model: list param is a COPY. append mutates the copy. Caller unchanged.

CPython result: data == [1, 2, 3, 99]
Model result:  data == [1, 2, 3]
"""


def add_element(xs: list[int], val: int) -> None:
    xs.append(val)


def main() -> None:
    data: list[int] = [1, 2, 3]
    add_element(data, 99)

    # CPython: data is [1, 2, 3, 99] — function mutated the SAME list
    # Model:  data is [1, 2, 3]     — function mutated a COPY
    assert data == [1, 2, 3, 99]  # True in CPython

    print(data)


main()
