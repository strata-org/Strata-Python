# Test: in a method of C, the binders __k and __v of a quantifier over items() are two names,
# _C__k and _C__v, which read the key and the value.
from pyhard import loop_invariant

class C:
    def m(self, d):
        i = 0
        loop_invariant(lambda: all(__k > 0 and __v < 0 for __k, __v in d.items()))
        while i < 1:
            i += 1
        return i

print(C().m({1: -1}))
