# Zero-argument super() and __class__: a method, a comprehension in a method (also one that
# rebinds the first parameter), a reassigned first parameter, a lambda in a class body, an
# explicit super(B, self), a local super, a decorated class, whose __class__ cell holds the
# undecorated class, and a class nested in a method, whose body reads the method's
# __class__.  A class body's own __class__ is a name.  Where CPython raises RuntimeError at
# run time (no positional parameter, or no class), the translator rejects super().  A
# deleted first parameter: super().m reads the cell first (LOAD_SUPER_ATTR), and a bare
# super() checks the parameter first and raises RuntimeError, as do super().__class__ and the
# targets super().x = and del super().y, which CPython compiles as plain calls.
def wrap(cls):
    return cls


class A:
    here = __class__

    def m(self, x):
        return x


@wrap
class B(A):
    def m(self, x):
        return super().m(x) + 1

    def names(self):
        return [super().m(i) for i in range(2)], __class__

    def two(self):
        return super(B, self).m(0)

    def bare_del(self):
        del self
        return super()

    def attr_del(self):
        del self
        return super().m(0)

    def cls_del(self):
        del self
        return super().__class__

    def store_del(self):
        del self
        super().x = 1
        del super().y

    def rebind(self, other):
        self = other
        return super().m(0), [super().m(self) for self in range(2)]

    f = lambda self: super().m(0)

    def local(self):
        super = len
        return super()

    def star(*args):
        return super()

    def kw(*, self):
        return super()

    x = super()

    def outer(self):
        class Inner:
            def n(self):
                return __class__
            y = __class__
        return Inner

    @staticmethod
    def s():
        return super()


def f(x):
    return super()
