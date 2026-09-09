# Test: isinstance(lst[0], int) then lst.insert(0, "x").
"""Test: isinstance(lst[0], int) then lst.insert(0, "x")."""


def main() -> None:
    lst: list[int | str] = [1, 2, 3]
    if isinstance(lst[0], int):
        lst.insert(0, "inserted")  # shifts elements
        # mypy: lst[0] is int (narrowed). Runtime: "inserted" (str)
        result: int = lst[0] - 1  # TypeError?


if __name__ == "__main__":
    main()
