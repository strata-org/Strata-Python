# Exercise symmetric receiver rejection for <=.
class C:
    x: int

    @admit(lambda self, result: self.x <= OLD(self.x))
    def m(self) -> int:
        ...
