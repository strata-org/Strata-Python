# Test: an item deletion on an object without __delitem__, with a key that is not an index
class A:
    pass
del A()["x"]
