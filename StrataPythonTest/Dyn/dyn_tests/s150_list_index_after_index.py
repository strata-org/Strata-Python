# A list's item write, delete and read check the index against the list's size after the
# index's __index__ ran, which may change the list.
class Clear:
    def __index__(self):
        del xs[0:2]
        return 0
xs = [1, 2]
try:
    xs[Clear()] = 5
except IndexError as e:
    print("IndexError")
print(len(xs))

class ClearAll:
    def __index__(self):
        del xs[:]
        return 0
xs = [1, 2]
try:
    del xs[ClearAll()]
except IndexError as e:
    print("IndexError")
print(len(xs))

class Last:
    def __index__(self):
        del xs[0:3]
        return -1
xs = [1, 2, 3]
try:
    xs[Last()] = 5
except IndexError as e:
    print("IndexError")
print(len(xs))

class Grow:
    def __index__(self):
        xs[len(xs):] = [9]
        return -1
xs = [1, 2, 3]
print(xs[Grow()])

class Shrink:
    def __index__(self):
        del xs[:]
        return 0
xs = [1, 2]
try:
    print(xs[Shrink()])
except IndexError as e:
    print("IndexError")

class Boom:
    def __index__(self):
        raise KeyError
xs = [1, 2]
try:
    xs[Boom()] = 0
except KeyError as e:
    print("KeyError", len(xs), xs[0], xs[1])
try:
    del xs[Boom()]
except KeyError as e:
    print("KeyError", len(xs), xs[0], xs[1])
