# Class instantiation: supported case. Known class, no metaclass, standard
# __new__, __init__ in source.
"""Class instantiation: supported case.
Known class, no metaclass, standard __new__, __init__ in source.
"""

class Point:
    __slots__ = ('x', 'y')

    def __init__(self, x: int, y: int) -> None:
        self.x = x
        self.y = y

def make_origin() -> Point:
    return Point(0, 0)

def make_point(x: int, y: int) -> Point:
    p = Point(x, y)
    assert p.x == x and p.y == y
    return p

if __name__ == "__main__":
    o = make_origin()
    print(o.x, o.y)  # 0 0

    p = make_point(3, 4)
    print(p.x, p.y)  # 3 4
