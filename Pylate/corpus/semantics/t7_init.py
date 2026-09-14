class Good:
    def __init__(self, a):
        self.x = a
        self.y = 0


class Lazy:
    def __init__(self):
        self.x = 1

    def warm(self):
        self.cache = self.x + 1


class Cond:
    def __init__(self, flag):
        self.a = 1
        if flag:
            self.b = 2


g = Good(5)
u = g.x + g.y

l = Lazy()
c = l.cache
l.warm()
d = l.cache

k = Cond(0)
e = k.b
