# Test: an exception raised while __hash__ is bound makes the value unhashable
class A:
    @property
    def __hash__(self):
        return 1 // 0
s = {A()}
