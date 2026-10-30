# A method named dict shadows the builtin in the rest of the class body, so in CPython the
# return annotation of m is the method, not the builtin dict.
class C:
    def dict(self) -> int:
        ...

    def m(self) -> dict:
        ...
