from pyhard import loop_invariant, OLD


def f(a, b, n, xs):
    i = 0
    n = n + 1
    loop_invariant(lambda: (OLD(a) if n > 0 else 0) >= 0 or True)
    loop_invariant(lambda: -(OLD(a) + n) <= 0 or True)
    loop_invariant(lambda: len(xs[OLD(a):n]) >= 0)
    loop_invariant(lambda: (OLD(a) if OLD(b) else 0) >= 0 or True)
    loop_invariant(lambda: len(OLD(xs)[OLD(a):]) >= 0 or True)
    while i < 2:
        i += 1
    return i


print(f(1, True, 2, [1, 2, 3]))
