from pyhard import loop_invariant, OLD

def f(n):
    i = 0
    loop_invariant(lambda: (i + 1) * 2 - 1 > 0 and i // 1 % 7 >= 0 and i ** 2 >= 0)
    loop_invariant(lambda: -i <= 0 and +i >= 0 and ~i < 0 and not i < 0 and i / 1 >= 0)
    while i < n:
        i += 1
    return i

print(f(2))
