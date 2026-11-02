# Test: l *= x when x.__index__ empties the list
l = [1, 2]


class I:
    def __index__(self):
        del l[:]
        return 2


l *= I()
try:
    l[0]
except IndexError:
    print("empty")
