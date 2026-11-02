# Test: an exception raised while a comparison dunder is bound counts as NotImplemented
class A:
    @property
    def __eq__(self):
        return 1 // 0
r = A() == 1
