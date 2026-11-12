from pyhard import loop_invariant, OLD
i = 0
loop_invariant(p=lambda: i <= 3)
while i < 3:
    i += 1
