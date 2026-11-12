from pyhard import loop_invariant, OLD

def f(n):
    c = 0
    loop_invariant(lambda: c >= 0)
    for i in range(n):
        for j in range(i):
            c += 1
    return c

print(f(4))
