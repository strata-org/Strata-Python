# Test: == of two one-item lists whose items' __eq__ returns NotImplemented calls it on both sides
n = 0
class C:
    def __eq__(self, o):
        global n
        n = n + 1
        return NotImplemented
print([C()] == [C()], n)
