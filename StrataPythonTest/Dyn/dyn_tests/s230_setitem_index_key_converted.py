# Test: an item write on an object without __setitem__ converts an index key first
class A:
    pass
class Big:
    def __index__(self):
        return 2 ** 70
A()[Big()] = 1
