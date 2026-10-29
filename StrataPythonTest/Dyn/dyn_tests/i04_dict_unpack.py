# Dict displays use a last-wins merge, unlike a call site's duplicate-key error.
a = {"x": 1}
b = {"x": 2, "y": 3}
print({**a})
print({**a, **b})
print({**a, "x": 9})
print({"z": 0, **b})
print({})
print(dict(a))
print(dict([("k", 1), ("j", 2)]))
print(dict(a, z=9))
print(dict())
