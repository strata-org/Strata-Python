# Method call: supported case. Known class, method defined in source, no
# monkey-patching.
"""Method call: supported case.
Known class, method defined in source, no monkey-patching.
"""

class Rectangle:
    __slots__ = ('width', 'height')

    def __init__(self, width: int, height: int) -> None:
        self.width = width
        self.height = height

    def area(self) -> int:
        return self.width * self.height

    def scale(self, factor: int) -> None:
        self.width *= factor
        self.height *= factor

if __name__ == "__main__":
    r = Rectangle(3, 4)
    print(r.area())   # 12
    r.scale(2)
    print(r.area())   # 48
