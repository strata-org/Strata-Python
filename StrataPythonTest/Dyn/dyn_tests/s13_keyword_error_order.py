# Test: a call with an unexpected keyword before a keyword that repeats a positional argument;
# CPython reports the unexpected keyword first
def k(a):
    return a
k(1, b=2, a=3)
