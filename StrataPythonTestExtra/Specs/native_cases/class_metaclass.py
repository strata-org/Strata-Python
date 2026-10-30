# A metaclass is a class keyword, which is not supported: the model is rejected.
class C(metaclass=type):
    x: int
