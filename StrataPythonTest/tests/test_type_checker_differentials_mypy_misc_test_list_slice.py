# Test: isinstance(lst[0], int) then lst[0:1] = ["hello"].
"""Test: isinstance(lst[0], int) then lst[0:1] = ["hello"]."""


def main() -> None:
    lst: list[int | str] = [1, 2, 3]
    if isinstance(lst[0], int):
        lst[0:1] = ["hello"]  # slice assignment replaces element
        # mypy: lst[0] is int (narrowed)? Runtime: "hello" (str)
        result: int = lst[0] - 1  # TypeError?


if __name__ == "__main__":
    main()
