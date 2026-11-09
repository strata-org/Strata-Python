# Test: f(**m) and {**m} over user mappings: keys(), a keys iterator over several activations, __getitem__, and the errors
class M:
    def keys(self):
        print("keys")
        return ["a", "b"]
    def __getitem__(self, k):
        print("getitem", k)
        return k * 2
class KI:
    def __iter__(self):
        print("KI.iter")
        return self
    def __init__(self):
        self.i = 0
    def __next__(self):
        self.i += 1
        if self.i > 2:
            raise StopIteration
        print("next", self.i)
        return ["k1", "k2"][self.i - 1]
    def __length_hint__(self):
        print("KI.hint")
        return 0
class M2:
    def keys(self):
        print("keys2")
        return KI()
    def __getitem__(self, k):
        print("getitem", k)
        return 1
def g(**kw):
    return kw
r = g(**M())
print(len(r), r["a"], r["b"])
r = g(**M2())
print(len(r), r["k1"], r["k2"])
d = {**M(), "c": 3}
print(len(d), d["a"], d["c"])
d = {"a": 0, **M()}
print(d["a"])
class Bad:
    def keys(self):
        return 5
for t in [lambda: print(**5), lambda: {**5}, lambda: print(**Bad()), lambda: print(**{"sep": 1}, **M2())]:
    try:
        t()
    except TypeError as e:
        print(e.args[0])
try:
    print(**{"a": 1}, **M())
except TypeError as e:
    print(e.args[0])
