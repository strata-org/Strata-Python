from pyhard import loop_invariant, OLD

def f(n):
    i = 0
    loop_invariant(lambda: later is None or i <= n)
    while i < n:
        later = None
        i += 1
    return i

print(f(2))
