from pyhard import loop_invariant, OLD

def f(n):
    i = 0
    loop_invariant(lambda: OLD(n, n) == n)
    while i < n:
        i += 1
    return i
