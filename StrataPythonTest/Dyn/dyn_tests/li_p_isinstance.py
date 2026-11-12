from pyhard import loop_invariant, OLD

class K:
    pass

def f(k, n):
    i = 0
    loop_invariant(lambda: isinstance(i, int) and isinstance(k, K))
    loop_invariant(lambda: isinstance(i, int) == True)
    while i < n:
        i += 1
    return i

print(f(K(), 2))
