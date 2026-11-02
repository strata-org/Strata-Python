# Test: type() with three arguments copies the namespace dict and doesn't add __doc__ to it
d = {"a": 1}
X = type("X", (), d)
d["a"] = 2
print(X.a, "__doc__" in d)
