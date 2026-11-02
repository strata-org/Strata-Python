# Test: l *= x repeats the list as it is after x.__index__ ran
l = [1, 2]


class I:
    def __index__(self):
        l[2:] = [3]
        return 2


l *= I()
print(l[0], l[2], l[3], l[5])
try:
    l[6]
except IndexError:
    print("6 items")
