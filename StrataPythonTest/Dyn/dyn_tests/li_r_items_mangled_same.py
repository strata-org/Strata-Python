# Test: in a method of C, the binders __k and _C__k are one name as CPython stores it, so the
# quantifier over items() binds only the value; it is rejected.
from pyhard import loop_invariant

class C:
    def m(self, d):
        i = 0
        loop_invariant(lambda: all(__k > 0 for __k, _C__k in d.items()))
        while i < 1:
            i += 1
        return i

print(C().m({1: -1}))
