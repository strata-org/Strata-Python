# A dict reverse iterator whose dict changed its keys at the same size stops with a gap.
d = {"x": 0, "y": 0, "z": 0}
it = reversed(d)
print(next(it))
del d["y"]
d["w"] = 0
for k in it:
    print(k)
