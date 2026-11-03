# CPython runs a class's own decorators outside its body, so it doesn't rename their names.
@invariant(lambda self: self.__x >= 0)
class C:
    def m(self) -> int:
        ...
