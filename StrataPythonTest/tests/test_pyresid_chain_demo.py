class Inner:
    def __init__(self, other_field: int):
        self.other_field = other_field


class Outer:
    def __init__(self, field: Inner):
        self.field = field


class P:
    def __init__(self, y: int):
        self.y = y


d = {"k": Outer(Inner(3))}
x = P(4)
key = "k"
r = d[key].field.other_field + x.y
