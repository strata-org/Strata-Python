# A class body reads its own names, then the enclosing function's, then globals and builtins.
# Its names are invisible to its methods.
g = 1


class C:
    a = 1
    b = a + g
    c = len

    def m(self):
        return a, b

    def n(self):
        return self.a


def outer():
    v = 1

    class D:
        w = v

        def m(self):
            return v, w
    return D
