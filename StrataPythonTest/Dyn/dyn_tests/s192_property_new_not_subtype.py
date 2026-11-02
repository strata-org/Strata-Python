# Test: property.__new__ of a class that is not a subtype of property
x = property.__new__(list)
print(type(x) is list)
