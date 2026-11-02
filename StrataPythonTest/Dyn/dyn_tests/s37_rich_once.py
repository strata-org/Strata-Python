# Test: == between an object whose __eq__ returns NotImplemented and an int calls that __eq__ once
n = 0
class C:
    def __eq__(self, other):
        global n
        n = n + 1
        return NotImplemented
r = C() == 1
print(r, n)
