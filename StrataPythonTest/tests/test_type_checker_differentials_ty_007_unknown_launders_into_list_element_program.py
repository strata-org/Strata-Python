# ty:           clean (no diagnostic)
# CPython:      TypeError (can only concatenate str (not "int") to str)
# mypy --strict: error [no-untyped-def, no-untyped-call]
#
# ty unsoundness (container channel): an Unknown value is laundered into a declared
# `list[int]` via `.append`. `src()` is Unknown (unannotated). ty accepts
# `xs.append(src())` because Unknown is assignable to `int`, and it does NOT re-tag
# `xs` or flag the append. `xs` stays `list[int]`, so `xs[0] + 1` is int + int.
# At runtime the element is "s" and `"s" + 1` raises TypeError. This is the
# list-element analog of 003/004: the wrong-typed value crosses the declared element
# type that ty trusts.

def src():
    return "s"

xs: list[int] = []
xs.append(src())
xs[0] + 1
