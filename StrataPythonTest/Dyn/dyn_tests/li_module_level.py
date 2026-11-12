from pyhard import loop_invariant, OLD

i = 0
total = 0
loop_invariant(lambda: total == 2 * i)
while i < 3:
    total += 2
    i += 1
print(total)
