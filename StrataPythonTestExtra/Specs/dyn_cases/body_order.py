# The class body binds its names in source order: y reads the global m, before the method m is
# bound.
def m() -> int:
    ...

class C:
    y = m
    def m(self) -> int:
        ...
