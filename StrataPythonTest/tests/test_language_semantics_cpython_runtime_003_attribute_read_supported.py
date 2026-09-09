# Attribute read: supported case. Class is closed, fields declared in
# __init__, no descriptors.
"""Attribute read: supported case.
Class is closed, fields declared in __init__, no descriptors.
"""

class Point:
    __slots__ = ('x', 'y')

    def __init__(self, x: int, y: int) -> None:
        self.x = x
        self.y = y

def get_x(p: Point) -> int:
    return p.x

def get_y(p: Point) -> int:
    return p.y

if __name__ == "__main__":
    p = Point(3, 7)
    print(get_x(p))  # 3
    print(get_y(p))  # 7
