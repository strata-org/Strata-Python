# Test: a __contains__ whose __get__ gives None makes the instance no container
class NoneGet:
    def __get__(self, obj, owner=None):
        return None
class A:
    __contains__ = NoneGet()
r = 1 in A()
