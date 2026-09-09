# ty:           clean (no diagnostic)
# CPython:      TypeError (can only concatenate str (not "int") to str)
# mypy --strict: error [no-untyped-def, no-untyped-call]
#
# ty unsoundness (iterable channel): iterating an Unknown yields an Unknown loop
# variable. `src()` is Unknown (unannotated), so `for x in src()` types `x` as
# Unknown, and `x + 1` is unchecked. At runtime `src()` is ["s"], the first element
# is "s", and `"s" + 1` raises TypeError. The Unknown laundering enters through the
# `for` iterable rather than a call/append/subscript -- completing the channel map.

def src():
    return ["s"]

total = 0
for x in src():
    total = x + 1
print(total)
