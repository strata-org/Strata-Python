# Test: < between an object whose __lt__ returns NotImplemented and an int calls it once, then raises TypeError
n = 0
class C:
    def __lt__(self, o):
        global n
        n = n + 1
        return NotImplemented
C() < 1
