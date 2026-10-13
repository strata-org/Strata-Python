# A class body's namespace is the mapping __prepare__ returns.  Every read first calls its
# __getitem__, also one that falls back to a global or a free variable, and a KeyError means
# absent.  A del that fails raises NameError.
class Ns(dict):
    def __getitem__(self, key):
        return dict.__getitem__(self, key)


class Meta(type):
    @classmethod
    def __prepare__(mcs, name, bases):
        return Ns()


x = 1


class C(metaclass=Meta):
    y = x
    z = y
    del z


def f():
    v = 2

    class D(metaclass=Meta):
        w = v
    return D
