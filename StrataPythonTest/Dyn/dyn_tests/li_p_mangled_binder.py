from pyhard import loop_invariant, OLD

class C:
    def f(self, xs):
        i = 0
        loop_invariant(lambda: all(__x > 0 for __x in xs))
        while i < len(xs):
            i += 1
        return i

print(C().f([1, 2]))
