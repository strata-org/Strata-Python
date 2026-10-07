# Private names in a class are mangled with the class name.
class _Foo:
    __a = 1
    __b__ = 2

    def __m(self, __p):
        __local = __p
        return __local, self.__a

    class __Inner:
        __c = 3
