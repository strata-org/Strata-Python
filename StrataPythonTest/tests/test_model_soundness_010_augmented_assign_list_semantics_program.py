# `+=` on list parameter: iadd mutates in place (caller sees it), but PAdd
# creates new value (caller doesn't)
"""
Augmented assignment `xs += [4]` on a list uses __iadd__ in CPython,
which mutates in place and returns self. The Laurel encoding desugars
this to `xs = PAdd(xs, [4])` which creates a NEW ListAny value via
List_extend — correct for the local variable, but wrong for any
function that received the list as a parameter.
"""

def extend_list(xs: list[int]) -> int:
    xs += [4]
    # CPython: xs.__iadd__([4]) mutates xs in place, returns self
    # The caller's list is also mutated (same object)
    return len(xs)

def main() -> None:
    nums: list[int] = [1, 2, 3]
    n: int = extend_list(nums)
    # CPython: nums is now [1, 2, 3, 4] because iadd mutated in place
    # Laurel: nums is still [1, 2, 3] because the parameter was passed
    #         by value (ListAny is a value type), and PAdd returned a
    #         new ListAny that was only assigned to the local `xs`
    print(len(nums))  # CPython: 4, Laurel: 3

main()
