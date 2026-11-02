# Test: deleting __weakref__, and writing it on a subclass of a class with slots
class E:
    pass
e = E()
try:
    del e.__weakref__
    print('deleted')
except AttributeError:
    print('AttributeError')
class S:
    __slots__ = ('a',)
class T(S):
    pass
t = T()
try:
    t.__weakref__ = 2
    print('set')
except AttributeError:
    print('AttributeError')
