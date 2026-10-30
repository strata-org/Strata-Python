# A method with *args is rejected: PySpec has no form for it.
class C:
    def m(self, *args: int) -> None:
        ...
