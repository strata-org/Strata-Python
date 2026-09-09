# `int * str` and `int * list` — no reflected dispatch; `PMul` has `str×int`
# case but not `int×str`, falls to Hole
"""
Python's `int * str` uses reflected method dispatch: int.__mul__(str) returns
NotImplemented, then str.__rmul__(int) is called. The Laurel model dispatches
by tag pattern matching with no reflected methods. PMul likely has a case for
str*int but NOT int*str — the operand order matters.
"""


def repeat_string(n: int, s: str) -> str:
    # int * str -> str (via str.__rmul__)
    return n * s


def pad_left(text: str, width: int) -> str:
    padding: int = width - len(text)
    if padding <= 0:
        return text
    # int * str for the spaces
    return padding * " " + text


def main() -> None:
    # str * int (normal order — likely modeled)
    a: str = "ab" * 3
    assert a == "ababab"

    # int * str (reversed — requires reflected dispatch)
    b: str = repeat_string(3, "ab")
    assert b == "ababab"

    # Same result, different operand order
    assert a == b

    # Practical use: padding
    c: str = pad_left("hi", 5)
    assert c == "   hi"

    print(a, b, c)


main()
