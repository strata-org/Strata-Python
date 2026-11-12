# A loop that updates every value of a dict with int keys after a deletion: its table holds keys
# that aren't strs, so CPython neither converts nor compacts it, and the model agrees.
d = {1: 0, 2: 0, 3: 0}
del d[1]
for k in d:
    d[k] = d[k] + 1
print(d)
