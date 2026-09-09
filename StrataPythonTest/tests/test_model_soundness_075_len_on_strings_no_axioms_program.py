# `len()` on strings has no axioms — `str_len` may be uninterpreted, making
# `len(s) >= 0` unprovable
"""
`len()` on strings returns the number of characters. The model needs
`str_len` mapped to SMT-LIB `str.len` for this to be provable. If
`len()` on `from_str` is uninterpreted or falls to Hole, basic string
length properties (len("") == 0, len(s) >= 0) are unprovable.
"""


def is_empty(s: str) -> bool:
    return len(s) == 0


def is_short(s: str, max_len: int) -> bool:
    return len(s) <= max_len


def pad_right(s: str, width: int) -> str:
    while len(s) < width:
        s = s + " "
    return s


def truncate(s: str, max_len: int) -> str:
    if len(s) <= max_len:
        return s
    # Can't slice (finding 068), so build manually
    result: str = ""
    i: int = 0
    while i < max_len:
        result = result + s[i]
        i = i + 1
    return result


def main() -> None:
    # Basic len
    assert len("") == 0
    assert len("hello") == 5
    assert len("a") == 1

    # len after concatenation
    a: str = "foo"
    b: str = "bar"
    assert len(a + b) == 6  # requires len(concat) == len(a) + len(b) axiom

    # is_empty
    assert is_empty("") == True
    assert is_empty("x") == False

    # Pad
    padded: str = pad_right("hi", 5)
    assert len(padded) == 5

    # Truncate
    short: str = truncate("hello world", 5)
    assert len(short) == 5

    # len is always non-negative (should be provable)
    s: str = "anything"
    assert len(s) >= 0

    print(len("hello"), len(a + b), is_empty(""))


main()
