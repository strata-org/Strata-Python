class Base:
    def __init__(self, x):
        self.x = x


class Sub(Base):
    def __init__(self, x):
        super().__init__(x)


o = Base(1)
v = getattr(o, "x")
setattr(o, "x", 2)
t = type(o)
e = eval("1 + 1")
