# Receiver prepending: bound methods and __init__ get self in the args tuple.
class K:
    def __init__(self, n, **opts):
        self.n = n
        self.opts = opts
    def show(self, tag, *extra, **kw):
        print(tag, self.n, len(self.opts), extra, kw)

k = K(5, color="red")
k.show("a")
k.show("b", 1, 2)
k.show("c", 1, k=2)
K(1).show("d")

class Base:
    def greet(self, who="world"):
        print("hello", who)
class Child(Base):
    pass
Child().greet()
Child().greet("there")
Child().greet(who="you")
