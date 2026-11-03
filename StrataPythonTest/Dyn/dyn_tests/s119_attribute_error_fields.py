# Test: an AttributeError raised without name and obj by __getattr__ stops with a gap
class C:
    def __getattr__(self, n):
        raise AttributeError("no " + n)
c = C()
try:
    c.q
except AttributeError as e:
    print(e.name, e.obj is c, e.args[0])
