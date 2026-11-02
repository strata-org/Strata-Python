# Test: a __hash__ whose __get__ gives None makes the instance unhashable
class NoneGet:
    def __get__(self, obj, owner=None):
        return None
class A:
    __hash__ = NoneGet()
s = {A()}
