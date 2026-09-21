# A class base cannot reference a class declared later.
class A(B):
    x: int


class B:
    y: int
