# A class that defines a method twice without @overload is rejected.
class C:
    def m(self) -> None:
        ...

    def m(self, x: int) -> None:
        ...
