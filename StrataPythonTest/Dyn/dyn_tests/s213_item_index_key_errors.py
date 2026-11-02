# Test: item assignment and deletion on an object of a class with neither dunder, with index keys whose __index__ is too large or raises
def err(f):
    try:
        return f()
    except Exception as e:
        return (type(e).__name__, e.args[0])
class Big:
    def __index__(self):
        return 2**100
class Boom:
    def __index__(self):
        raise KeyError('boom')
class A:
    pass

def s1():
    A()[Big()] = 1
def s2():
    del A()[Big()]
def s3():
    A()[Boom()] = 1
def s4():
    del A()[Boom()]
r1 = err(s1)
r2 = err(s2)
r3 = err(s3)
r4 = err(s4)
for r in (r1, r2, r3, r4):
    print(r[0], r[1])
