# Decorators on a nested class are not supported: the model is rejected.
class Outer:
    @exhaustive
    class Inner:
        x: int
