# A write of an existing str key through an equal object that isn't a str: CPython converts the
# dict's table of str keys to a general one, which compacts it after a deletion, so the comparison
# skips an entry; the model stops with a gap.
class K:
    def __hash__(self):
        return "q".__hash__()
    def __eq__(self, o):
        return o == "q"
class A:
    def __init__(self, v):
        self.v = v
    def __eq__(self, o):
        print("eq", self.v)
        if self.v == 1:
            a[K()] = A(9)
        return True
a = {"x": 0, "p": A(1), "q": A(2), "r": A(3)}
del a["x"]
b = {"p": 0, "q": 0, "r": 0}
print(a == b)
