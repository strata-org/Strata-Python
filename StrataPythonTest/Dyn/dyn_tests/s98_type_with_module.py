# Test: type() with __module__ and __qualname__ in its namespace dict, which it copies and leaves unchanged
d = {"a": 1, "__module__": "m", "__qualname__": "Q"}
X = type("X", (), d)
d["a"] = 2
print(X.a, "__doc__" in d, "__qualname__" in d, X.__module__, X.__qualname__)
