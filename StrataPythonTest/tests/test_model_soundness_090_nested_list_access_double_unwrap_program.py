# Nested list access (`matrix[i][j]`) requires double unwrap — intermediate
# `isfrom_ListAny` tag check needed
"""
A nested list (`list[list[int]]`) stores ListAny values inside a ListAny.
Accessing an element returns `Any` which must be unwrapped as `from_ListAny`
before the inner list can be indexed. This requires:
1. List_get on outer list → returns Any
2. Assert/check that result is from_ListAny
3. Unwrap: as_ListAny(result)
4. List_get on inner list → returns Any
5. Assert/check that result is from_int

If the translator doesn't insert the intermediate unwrap, or if the
type tag assertion fails, nested list access breaks.
"""


def get_element(matrix: list[list[int]], row: int, col: int) -> int:
    return matrix[row][col]


def sum_row(matrix: list[list[int]], row: int) -> int:
    total: int = 0
    r: list[int] = matrix[row]
    i: int = 0
    while i < len(r):
        total = total + r[i]
        i = i + 1
    return total


def sum_all(matrix: list[list[int]]) -> int:
    total: int = 0
    for row in matrix:
        for val in row:
            total = total + val
    return total


def transpose_2x3(m: list[list[int]]) -> list[list[int]]:
    """Transpose a 2x3 matrix to 3x2."""
    r0: list[int] = [m[0][0], m[1][0]]
    r1: list[int] = [m[0][1], m[1][1]]
    r2: list[int] = [m[0][2], m[1][2]]
    return [r0, r1, r2]


def main() -> None:
    matrix: list[list[int]] = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]

    # Double indexing
    assert get_element(matrix, 0, 0) == 1
    assert get_element(matrix, 1, 2) == 6
    assert get_element(matrix, 2, 1) == 8

    # Sum a row
    assert sum_row(matrix, 0) == 6   # 1+2+3
    assert sum_row(matrix, 1) == 15  # 4+5+6

    # Sum all
    assert sum_all(matrix) == 45  # 1+2+...+9

    # Transpose
    m: list[list[int]] = [[1, 2, 3], [4, 5, 6]]
    t: list[list[int]] = transpose_2x3(m)
    assert t[0] == [1, 4]
    assert t[1] == [2, 5]
    assert t[2] == [3, 6]

    print(get_element(matrix, 1, 1), sum_all(matrix))


main()
