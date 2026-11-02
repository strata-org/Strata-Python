# Test: an index that a C ssize_t can't hold names the key's type in the IndexError
class Big:
    def __index__(self):
        return 2 ** 70
r = [1][Big()]
