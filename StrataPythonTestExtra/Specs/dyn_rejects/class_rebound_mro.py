class A:
    pass

class B:
    pass

class X(A, B):
    pass

class Y(B, A):
    pass

class Z(X, Y):
    pass

def Z() -> int:
    ...
