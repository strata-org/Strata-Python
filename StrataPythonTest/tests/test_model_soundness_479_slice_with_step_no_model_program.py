# SLICE WITH STEP PARAMETER — NO MODEL FOR THREE-ARGUMENT SLICE
"""
SLICE WITH STEP PARAMETER — NO MODEL FOR THREE-ARGUMENT SLICE

The subset allows:
  - List subscript (IN)
  - String subscript (IN)
  - Slice syntax s[a:b] (findings 068/324 identify no model)

The NOVEL gap: slicing with a STEP parameter `s[a:b:c]` or `lst[::2]`
is syntactically valid (same Slice AST node) but has ADDITIONAL semantics
beyond basic two-argument slicing:
  - `lst[::2]` → every other element
  - `lst[::-1]` → reversed list
  - `s[::2]` → every other character

Even if basic slicing `s[a:b]` gets a model (SMT-LIB str.substr), the
step parameter requires a fundamentally different operation — it's not
a contiguous substring/sublist but a STRIDED selection.

CPython: lst = [0,1,2,3,4,5]; lst[::2] → [0, 2, 4]
Model:   No slice operation at all → Hole
         Even with basic slice model: no stride → Hole or wrong result

DISTINCT FROM:
  - Finding 068 (list slice no model) — covers [a:b] only, no step
  - Finding 324 (string slice no model) — covers [a:b] only, no step
  - Finding 431 (negative index wraps) — single index, not slice

ROOT CAUSE: The Slice AST node has three optional fields (lower, upper, step).
Findings 068/324 address the case where step is None. When step is present,
a completely different algorithm is needed (strided selection), and no
Laurel operation exists for it.
"""


def every_other_element(lst: list[int]) -> list[int]:
    """lst[::2] selects elements at even indices."""
    return lst[::2]
    # CPython: [10,20,30,40,50][::2] → [10, 30, 50]
    # Model: no slice-with-step → Hole


def reverse_list_via_slice(lst: list[int]) -> list[int]:
    """lst[::-1] reverses the list."""
    return lst[::-1]
    # CPython: [1,2,3][::-1] → [3, 2, 1]
    # Model: Hole (no stride operation)


def reverse_string(s: str) -> str:
    """s[::-1] reverses a string — common Python idiom."""
    return s[::-1]
    # CPython: "hello"[::-1] → "olleh"
    # Model: Hole


def skip_elements(lst: list[int], step: int) -> list[int]:
    """lst[::step] with variable step."""
    return lst[::step]
    # CPython: [0,1,2,3,4,5][::3] → [0, 3]
    # Model: Hole


def slice_with_all_three(lst: list[int]) -> list[int]:
    """lst[start:stop:step] — full three-argument slice."""
    return lst[1:5:2]
    # CPython: [0,1,2,3,4,5][1:5:2] → [1, 3]
    # Model: Hole


def is_palindrome(s: str) -> bool:
    """Common idiom: s == s[::-1] checks palindrome."""
    return s == s[::-1]
    # CPython: "racecar" == "racecar"[::-1] → True
    # Model: s == Hole → Hole (comparison with Hole)


def main() -> None:
    assert every_other_element([10, 20, 30, 40, 50]) == [10, 30, 50]
    assert reverse_list_via_slice([1, 2, 3]) == [3, 2, 1]
    assert reverse_string("hello") == "olleh"
    assert skip_elements([0, 1, 2, 3, 4, 5], 3) == [0, 3]
    assert slice_with_all_three([0, 1, 2, 3, 4, 5]) == [1, 3]
    assert is_palindrome("racecar") == True
    assert is_palindrome("hello") == False
    print("All passed")


main()
