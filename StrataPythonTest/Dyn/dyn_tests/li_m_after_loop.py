from pyhard import loop_invariant, OLD
i = 0
while i < 3:
    i += 1
loop_invariant(lambda: i <= 3)
