from pyhard import loop_invariant

def f(n):
    i = 0
    loop_invariant(lambda: OLD(n) == n)
    while i < n:
        i += 1
    return i
