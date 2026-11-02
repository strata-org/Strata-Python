# Test: the dunders of None, read as attributes of the object None
x = None
print(x.__class__ is type(None))
r = x.__repr__
print(r())
print(x.__bool__())
print(x.__init__())
print(x.__ne__(1))
