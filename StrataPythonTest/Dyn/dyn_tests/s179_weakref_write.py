# Test: a write to a user object's __weakref__, which a descriptor in its class's namespace refuses
class E:
    pass
e = E()
try:
    e.__weakref__ = 1
    print('set')
except AttributeError:
    print('AttributeError on write')
try:
    print(e.__weakref__)
except AttributeError:
    print('AttributeError on read')
