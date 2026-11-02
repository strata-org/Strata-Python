# Test: == of two objects whose __eq__ returns NotImplemented calls it on both sides, then compares identity
n = 0
class C:
    def __eq__(self, other):
        global n
        n = n + 1
        return NotImplemented
r = C() == C()
print(r, n)
