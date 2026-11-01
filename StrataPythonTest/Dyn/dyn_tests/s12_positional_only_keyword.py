# Test: a positional-only parameter passed by keyword, which stops with a gap (CPython
# reports it with its own message)
def h(a, /):
    return a
h(a=1)
