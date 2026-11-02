# Test: tuple.__eq__ stored in a class and called through an instance that is not a tuple raises TypeError
class C:
    eq = tuple.__eq__
print(C().eq((1,)))
