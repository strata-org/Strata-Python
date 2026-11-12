from pyhard import loop_invariant, OLD

def f(n):
    c = 0
    i = 0
    while i < n:
        loop_invariant(lambda: c >= 0)
        for j in range(i):
            c += 1
        i += 1
    return c

print(f(3))
