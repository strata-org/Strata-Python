# Test: an item deletion on an object without __delitem__, with an index key
class A:
    pass
del A()[0]
