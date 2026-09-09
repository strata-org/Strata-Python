# String slicing `s[1:3]` has no model — no `str_slice`; maps to SMT-LIB
# `str.substr` but translation missing
"""
String slicing s[a:b] has no model — no str_slice operation.

Finding 068 covers list slicing (no List_slice). This finding covers
the same gap for strings. String slicing is extremely common:
  s[1:3]   → "el"     (substring from index 1 to 3, exclusive)
  s[:3]    → "hel"    (first 3 characters)
  s[2:]    → "llo"    (from index 2 to end)
  s[-2:]   → "lo"     (last 2 characters)

The model has no str_slice/str_substr operation. The Subscript AST node
with a Slice value (not just an integer index) has no translation for
string-typed containers.

This maps directly to SMT-LIB str.substr(s, offset, length), so the
fix is straightforward — but the translation doesn't exist yet.

Uses ONLY confirmed-accepted constructs: str, int, subscript/slice, len.
"""


def first_n(s: str, n: int) -> str:
    """s[:n] returns first n characters."""
    return s[:n]
    # CPython: "hello"[:3] → "hel"
    # Model: no str_slice → Hole


def last_n(s: str, n: int) -> str:
    """s[-n:] returns last n characters."""
    return s[-n:]
    # CPython: "hello"[-2:] → "lo"
    # Model: Hole (no slice + no negative index wrap)


def middle(s: str, start: int, end: int) -> str:
    """s[start:end] returns substring."""
    return s[start:end]
    # CPython: "hello"[1:4] → "ell"
    # Model: Hole


def slice_length(s: str, a: int, b: int) -> bool:
    """len(s[a:b]) == b - a for valid indices."""
    sub: str = s[a:b]
    return len(sub) == b - a
    # CPython: True for 0 <= a <= b <= len(s)
    # Model: len(Hole) is Hole, comparison is unknown


def split_and_rejoin(s: str, i: int) -> bool:
    """s[:i] + s[i:] == s — fundamental slice property."""
    left: str = s[:i]
    right: str = s[i:]
    return left + right == s
    # CPython: True for 0 <= i <= len(s)
    # Model: Hole + Hole == s → unknown


def extract_extension(filename: str) -> str:
    """Common pattern: extract file extension."""
    dot_pos: int = filename.find(".")
    if dot_pos >= 0:
        return filename[dot_pos:]
    return ""
    # CPython: "file.py" → ".py"
    # Model: find returns Hole (finding 134), slice returns Hole


def main() -> None:
    assert first_n("hello", 3) == "hel"
    assert last_n("hello", 2) == "lo"
    assert middle("hello", 1, 4) == "ell"
    assert slice_length("hello", 1, 4) == True
    assert split_and_rejoin("hello", 2) == True
    assert extract_extension("file.py") == ".py"
