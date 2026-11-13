from pyhard import loop_invariant, OLD

n = 2
i = 0
loop_invariant(lambda: OLD(n) == n)
while i < n:
    i += 1
