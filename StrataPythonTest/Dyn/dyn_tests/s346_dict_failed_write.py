# A write whose key lookup raises: CPython converts the str-keys table (and compacts it) before the
# lookup, so the comparison skips an entry even though the write failed; the model stops with a gap.
class K:
    def __hash__(self):
        return "q".__hash__()
    def __eq__(self, o):
        raise ValueError("no")
class A:
    def __init__(self, v):
        self.v = v
    def __eq__(self, o):
        print("eq", self.v)
        if self.v == 1:
            try:
                a[K()] = 0
            except ValueError:
                print("raised")
        return True
a = {"x": 0, "p": A(1), "q": A(2), "r": A(3)}
del a["x"]
b = {"p": 0, "q": 0, "r": 0}
print(a == b)
