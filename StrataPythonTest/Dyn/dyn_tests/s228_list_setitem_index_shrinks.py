# Test: a list's item write checks the index against the list as the key's __index__ left it
class Shrink:
    def __index__(self):
        xs[1:] = []
        return 1
xs = [1, 2, 3]
xs[Shrink()] = 7
