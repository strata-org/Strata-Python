from pyhard import loop_invariant

x = 7
xs = [1, 2]
ys = [x for x in xs]
i = 0
loop_invariant(lambda: x == 7)
while i < 1:
    i += 1
print(ys, (lambda: x == 7)())
