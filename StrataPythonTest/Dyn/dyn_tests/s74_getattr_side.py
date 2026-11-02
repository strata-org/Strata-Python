# Test: __getattr__ runs once for each read of a missing attribute
n = 0
class C:
    def __getattr__(self, name):
        global n
        n = n + 1
        return n
c = C()
print(c.a, c.b, n)
