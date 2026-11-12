from pyhard import loop_invariant, OLD

def f(xs, n):
    i = 0
    loop_invariant(lambda: 0 <= i <= n and xs is not None and xs is xs and n != -1)
    loop_invariant(lambda: (i in xs or i not in xs) and i >= 0 and i < n + 1)
    while i < n:
        i += 1
    return i

print(f([0, 1], 2))
