# Test: a property without a setter, read on an instance
class C:
    @property
    def x(self):
        return 1
print(C().x)
