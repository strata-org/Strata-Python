# Class keywords on a nested class are not supported: the model is rejected.
class Outer:
    class Inner(flag=1):
        x: int
