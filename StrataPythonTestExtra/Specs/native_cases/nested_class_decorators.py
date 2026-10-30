# A nested class's @exhaustive and @invariant are read as a top-level class's.
class Outer:
    @exhaustive
    @invariant(lambda self: self.x >= 0)
    class Inner:
        x: int
