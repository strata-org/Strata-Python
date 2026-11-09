# Test: a dict whose keys change at the same size during its iteration stops with a gap
d = {1: 1, 2: 2, 3: 3}
it = iter(d)
print(next(it))
del d[1]
d[1] = 9
for k in it:
    print(k)
