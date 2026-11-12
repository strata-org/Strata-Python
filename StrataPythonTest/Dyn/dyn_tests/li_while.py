from pyhard import loop_invariant, OLD

def double(n):
    total = 0
    i = 0
    loop_invariant(lambda: 0 <= i <= n)
    loop_invariant(lambda: total == 2 * i)
    while i < n:
        total += 2
        i += 1
    return total

print(double(3))
