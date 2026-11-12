from pyhard import loop_invariant, OLD

def f(n):
    s = 0
    loop_invariant(lambda: s >= 0)
    for k in range(n):
        s += k
    return s

print(f(4))
