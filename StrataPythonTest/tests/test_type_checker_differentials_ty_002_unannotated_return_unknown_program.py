# ty:           clean (no diagnostic)
# CPython:      TypeError (can only concatenate str (not "int") to str)
# mypy --strict: error [no-untyped-def, no-untyped-call]
#
# ty unsoundness: a function with no return annotation has its return type
# inferred. The embedded ty does not propagate a precise-enough type to flag
# `get() + 1`: the call result is treated as Unknown/Any, so `<Unknown> + 1` is
# accepted. At runtime `get()` is "s" and `"s" + 1` raises TypeError.

def get():
    return "s"

get() + 1
