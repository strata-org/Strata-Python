# Test: a class made by type() with three arguments takes its __module__ from the caller's globals
X = type("X", (), {})
print(X.__module__)
