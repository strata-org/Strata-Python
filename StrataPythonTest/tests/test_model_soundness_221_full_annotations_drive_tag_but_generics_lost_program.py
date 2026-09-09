# Generic element types lost after container access — `xs: list[int]` emits
# `isfrom_ListAny(xs)` but `xs[i]` has no `isfrom_int` assertion
"""
"Full annotations" means every parameter and return type is annotated.
The model uses these to emit tag assertions: `x: int` → `assert isfrom_int(x)`.

But for GENERIC containers like `list[int]`, the annotation says the
LIST contains ints. The model knows `x` is `from_ListAny` but does it
know that ELEMENTS are `from_int`?

If not, after `val = xs[0]`, the model knows `val` is `Any` (could be
anything) even though the annotation says `xs: list[int]` guarantees
elements are int.

The annotation `list[int]` must generate:
  1. `assert isfrom_ListAny(xs)` — xs is a list
  2. For each element access `xs[i]`: `assert isfrom_int(xs[i])` — element is int

Without (2), element types are lost after extraction from the container.

Uses ONLY confirmed-accepted constructs: list[int], dict[str, int], int.
"""


def sum_list(xs: list[int]) -> int:
    """xs: list[int] — each element must be known as int."""
    total: int = 0
    for x in xs:
        # x should be known as int (from list[int] annotation)
        total = total + x  # PAdd(from_int, from_int) — needs x to be int
    return total


def first_element(xs: list[int]) -> int:
    """xs[0] must be known as int."""
    return xs[0]  # List_get returns Any; must assert isfrom_int


def dict_value_type(d: dict[str, int]) -> int:
    """d["key"] must be known as int."""
    return d["key"]  # DictStrAny_get returns Any; must assert isfrom_int


def list_of_strings(xs: list[str]) -> str:
    """Element type is str."""
    return xs[0]  # must assert isfrom_str


def nested_list_type(matrix: list[list[int]]) -> int:
    """matrix[i] is list[int], matrix[i][j] is int."""
    row: list[int] = matrix[0]  # must assert isfrom_ListAny
    return row[0]  # must assert isfrom_int


def main() -> None:
    assert sum_list([1, 2, 3, 4, 5]) == 15
    assert first_element([10, 20, 30]) == 10
    assert dict_value_type({"key": 42}) == 42
    assert list_of_strings(["hello", "world"]) == "hello"
    assert nested_list_type([[1, 2], [3, 4]]) == 1

    print(sum_list([1, 2, 3]), first_element([10]),
          dict_value_type({"key": 99}))


main()
