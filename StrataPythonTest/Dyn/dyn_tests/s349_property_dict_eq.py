# The __dict__ of an instance of a subclass of property is a split table in CPython, so == walks
# its class's shared keys, in the order the first instance set them; the model stops with a gap.
class V:
    def __init__(self, n):
        self.n = n
    def __eq__(self, o):
        print("eq", self.n)
        return True
class P(property):
    pass
e1 = property.__new__(P)
e1.b = 1
e1.a = 1
e2 = property.__new__(P)
e2.a = V("a")
e2.b = V("b")
e3 = property.__new__(P)
e3.a = V("a3")
e3.b = V("b3")
print(e2.__dict__ == e3.__dict__)
