# ty:           clean (no diagnostic)
# CPython:      TypeError (can only concatenate str (not "int") to str)
# mypy --strict: error [no-untyped-def, no-untyped-call]
#
# ty unsoundness (dict-value channel): an Unknown value is laundered into a declared
# `dict[str, int]` via subscript assignment. `d["k"] = src()` (Unknown) is accepted
# against the `int` value type; ty keeps `d["k"]` typed `int`, so `d["k"] + 1` is
# int + int. At runtime the stored value is "s" -> TypeError. Same trust failure as
# 007, through the dict value type instead of the list element type.

def src():
    return "s"

d: dict[str, int] = {}
d["k"] = src()
d["k"] + 1
