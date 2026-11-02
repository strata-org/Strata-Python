# Test: a list's *= with a count that has __index__ repeats the list in place
class Two:
    def __index__(self):
        return 2
xs = [1, 2]
ys = xs
xs *= Two()
same = xs is ys
