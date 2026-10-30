# The class variable m takes the method's name, so the class facts and the namespace would differ.
def g() -> int:
    ...

class C:
    def m(self) -> int:
        ...
    m = g
