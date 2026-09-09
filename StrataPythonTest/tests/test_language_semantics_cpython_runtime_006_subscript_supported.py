# Subscript: supported case. Container type is known, so slot dispatch
# collapses to direct access.
"""Subscript: supported case.
Container type is known, so slot dispatch collapses to direct access.
"""

def list_access(lst: list[int], i: int) -> int:
    return lst[i]

def dict_access(d: dict[str, int], key: str) -> int:
    return d[key]

def list_write(lst: list[int], i: int, v: int) -> None:
    lst[i] = v

if __name__ == "__main__":
    nums = [10, 20, 30]
    print(list_access(nums, 1))  # 20

    data = {"a": 1, "b": 2}
    print(dict_access(data, "b"))  # 2

    list_write(nums, 0, 99)
    print(nums)  # [99, 20, 30]
