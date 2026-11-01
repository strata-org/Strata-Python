# Test: a call that misses two keyword-only arguments, which CPython's message names
# both
def g(*, j, k):
    return j
g()
