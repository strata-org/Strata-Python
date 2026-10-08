# Inside a class, an attribute name is mangled as CPython does: `self.__a` reads `_C__a`, also
# in a nested function, but `self.__a__` is not mangled, nor is a keyword argument name
# (`f(__k=1)` passes `__k`).  Classes are rejected for now, so this pins the rejection.
class C:
    def m(self):
        f(__k=1)
        def h():
            return self.__b
        return self.__a, self.__a__, h()
