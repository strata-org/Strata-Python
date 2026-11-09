# A list's slice read, delete and write clamp the slice to the list's size after the bounds'
# __index__ ran, which may change the list.
class Drop:
    def __index__(self):
        del xs[0:4]
        return 3
xs = [1, 2, 3, 4]
del xs[Drop():]
print(len(xs))

class Insert:
    def __index__(self):
        xs[0:0] = [0]
        return 2
xs = [1, 2, 3, 4]
del xs[::Insert()]
print(len(xs), xs[0])

class Append:
    def __index__(self):
        xs[len(xs):] = [9]
        return 0
class Back:
    def __index__(self):
        return -1
xs = [1, 2, 3]
ys = xs[Append():Back()]
print(len(ys), ys[0], ys[2])

class Cut:
    def __index__(self):
        del xs[1:]
        return 3
xs = [1, 2, 3, 4]
xs[1:Cut()] = [7]
print(len(xs), xs[1])

class Boom:
    def __index__(self):
        raise KeyError
xs = [1, 2]
try:
    del xs[Boom():]
except KeyError as e:
    print("KeyError", len(xs), xs[0], xs[1])
try:
    xs[:Boom()] = [5]
except KeyError as e:
    print("KeyError", len(xs), xs[0], xs[1])
