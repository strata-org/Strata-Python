# == of an instance's __dict__ walks the class's shared keys, in the order the first instance set
# them, so CPython compares a before b here; the model stops with a gap.
class P:
    def __init__(self, n):
        self.n = n
    def __eq__(self, o):
        print("eq", self.n)
        return True
class C:
    pass
x = C()
x.a = P(1)
x.b = P(2)
y = C()
y.b = P(3)
y.a = P(4)
print(y.__dict__ == {"a": 0, "b": 0})
