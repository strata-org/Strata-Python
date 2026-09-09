# ty:           clean (no diagnostic)
# CPython:      TypeError ('int' object is not subscriptable)
# mypy --strict: error [no-untyped-def, no-untyped-call]
#
# ty unsoundness: an unannotated parameter is inferred as Unknown (ty's implicit
# `Any`). `xs[0]` on Unknown is Unknown, and the call `first(5)` is accepted
# because Unknown absorbs any argument. At runtime `5[0]` raises TypeError.
# (Variant: replace `xs[0]` with `xs.bit_length()` and call `first("s")` ->
#  AttributeError, same mechanism: attribute access on Unknown is unchecked.)

def first(xs):
    return xs[0]

first(5)
