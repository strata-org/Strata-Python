from pyhard import loop_invariant, OLD
i = 0
ps = [lambda: i <= 3]
loop_invariant(*ps)
while i < 3:
    i += 1
