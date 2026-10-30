# A metaclass on a nested class is a class keyword, which is not supported: the model is
# rejected.
class Outer:
    class Inner(metaclass=type):
        x: int
