# Test: a property with a setter, written and read on an instance
class C:
    @property
    def x(self):
        return self._x
    @x.setter
    def x(self, v):
        self._x = v
c = C()
c.x = 3
print(c.x)
