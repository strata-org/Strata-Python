from pyhard import loop_invariant, OLD

def f(n):
    c = 0
    i = 0
    loop_invariant(lambda: 0 <= i <= n)
    while i < n:
        j = 0
        loop_invariant(lambda: 0 <= j <= i)
        while j < i:
            c += 1
            j += 1
        i += 1
    return c

print(f(4))
