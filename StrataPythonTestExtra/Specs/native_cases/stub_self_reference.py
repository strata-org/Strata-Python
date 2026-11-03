# PySpec reads an annotation as a stub type: inside the class C, C means the class.
class C:
    def m(self, other: C) -> C:
        ...
