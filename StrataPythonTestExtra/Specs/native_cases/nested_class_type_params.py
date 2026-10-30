# Type parameters on a nested class are not supported: the model is rejected.
class Outer:
    class Inner[T]:
        x: int
