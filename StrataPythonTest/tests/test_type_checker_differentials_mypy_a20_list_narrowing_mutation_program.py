# isinstance narrows `obj.items: list[int] | str` to `list[int]`. A method
# call changes `obj.items` to `str`. Subsequent list operations (subscript
# `[0]`) operate on str instead of list, producing TypeError.
"""
a20_list_narrowing_mutation.py — isinstance narrows union field containing list, method mutates to str.

obj.items: list[int] | str is narrowed to list[int] via isinstance.
A method call changes obj.items to str. Subsequent list operations
(subscript) fail with TypeError.

mypy --strict: Success (0 errors)
Runtime: TypeError — can only concatenate str (not "int") to str
"""


class Container:
    def __init__(self) -> None:
        self.items: list[int] | str = [1, 2, 3]

    def stringify(self) -> int:
        self.items = "not a list"
        return 0


def main() -> None:
    c = Container()
    if isinstance(c.items, list):
        _ = c.stringify()  # mutates c.items to str
        # mypy: c.items is list[int] (narrowed). Runtime: "not a list" (str)
        val: int = c.items[0] + 1  # TypeError: can only concatenate str to str


if __name__ == "__main__":
    main()
