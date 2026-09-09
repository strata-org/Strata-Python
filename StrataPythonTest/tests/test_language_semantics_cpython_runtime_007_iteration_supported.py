# Iteration: supported case. Container type is known, so iterator protocol
# collapses to index loop.
"""Iteration: supported case.
Container type is known, so iterator protocol collapses to index loop.
"""

def sum_list(lst: list[int]) -> int:
    total = 0
    for x in lst:
        total += x
    return total

def count_range(n: int) -> int:
    total = 0
    for i in range(n):
        total += i
    return total

if __name__ == "__main__":
    print(sum_list([1, 2, 3, 4]))  # 10
    print(count_range(5))           # 10
