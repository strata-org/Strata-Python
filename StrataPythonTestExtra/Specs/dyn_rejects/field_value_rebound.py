# The class body binds x twice: as a field with a value, and as a method.
class C:
    x: int = 0

    def x(self) -> int:
        ...
