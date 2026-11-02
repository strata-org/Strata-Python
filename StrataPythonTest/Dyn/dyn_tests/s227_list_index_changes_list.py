# Test: a list's item read after an __index__ that changes the list reads the list as it is then
class Change:
    def __index__(self):
        xs[0] = 9
        return 0
xs = [1, 2, 3]
r = xs[Change()]
