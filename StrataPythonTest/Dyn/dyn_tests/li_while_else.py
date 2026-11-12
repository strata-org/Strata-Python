from pyhard import loop_invariant, OLD

def f(n):
    i = 0
    loop_invariant(lambda: i <= n)
    while i < n:
        i += 1
    else:
        i = -i
    return i

print(f(2))
