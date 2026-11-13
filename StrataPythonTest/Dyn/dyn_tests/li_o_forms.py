from pyhard import loop_invariant, OLD


class Acc:
    def __init__(self):
        self.total = 0

    def add(self, xs, __k=1, *rest):
        i = 0
        loop_invariant(lambda: self.total >= OLD(self.total) and OLD(self).total >= 0)
        loop_invariant(lambda: OLD(-__k) < 0 and OLD(__k if xs else 0) >= 0)
        loop_invariant(lambda: len(OLD(xs[0:1])) <= 1 and (OLD(__k > 0 and __k < 9) or True))
        while i < len(xs):
            self.total += xs[i] * __k
            i += 1
        return self.total

    # `is` inside OLD. On the machine, `rest is rest` stops with a gap, so this invariant is in a
    # method that the program calls after `add`, where the gap can't stop `add`'s invariants.
    def same(self, xs, *rest):
        i = 0
        loop_invariant(lambda: OLD(rest is rest) and OLD(xs is None) == False or True)
        while i < len(xs):
            i += 1
        return i


acc = Acc()
print(acc.add([1, 2], 2))
print(acc.same([1]))
