class Vec:
    def __init__(self, x: int, y: int):
        self.x = x
        self.y = y

    def __add__(self, other) -> "Vec":
        return Vec(self.x + other.x, self.y + other.y)

    def __eq__(self, other) -> bool:
        return self.x == other.x


class Flag:
    def __init__(self, on: int):
        self.on = on

    def __bool__(self) -> bool:
        return self.on > 0


a = Vec(1, 2)
b = Vec(3, 4)
c = a + b
d = c.x + c.y
e = a == b
f = a < b
g = a[0]

h = Vec(5, 6) if d > 0 else None
if h:
    i = h.x
else:
    j = h

fl = Flag(1)
if fl:
    k = fl.on
