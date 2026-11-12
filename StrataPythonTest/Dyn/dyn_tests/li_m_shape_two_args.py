from pyhard import loop_invariant, OLD
i = 0
loop_invariant(lambda: i <= 3, print())
while i < 3:
    i += 1
