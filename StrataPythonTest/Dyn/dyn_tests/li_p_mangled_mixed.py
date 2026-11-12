from pyhard import loop_invariant

_C__x = -5

class C:
    def m(self, xs):
        i = 0
        loop_invariant(lambda: all(_C__x > 0 for __x in xs))
        while i < 1:
            i += 1
        return i

print(C().m([1, 2]))
