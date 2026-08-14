# Method receiver fields are rejected before Laurel lowering.
class C:
    x: int

    @admit(lambda self, result: self.x >= OLD(self.x))
    def m(self) -> int:
        ...
