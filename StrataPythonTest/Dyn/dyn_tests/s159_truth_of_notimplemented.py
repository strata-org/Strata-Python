# Test: the truth of NotImplemented warns, and the warning registers itself
print(not NotImplemented)
print("__warningregistry__" in globals())
