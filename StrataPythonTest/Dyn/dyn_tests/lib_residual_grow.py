# A looping built-in reached inside an operation stops with a gap when user code grows the list
# past the walk's bound.
l = []


class Grow:
    def __bool__(self):
        if len(l) < 6:
            l[len(l):] = [Grow()]
        return False


l[0:0] = [Grow(), Grow()]


class C:
    __radd__ = staticmethod(any)


print(sum([C()], iter(l)), len(l))
