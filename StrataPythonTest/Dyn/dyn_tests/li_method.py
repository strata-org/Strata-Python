from pyhard import loop_invariant, OLD

class Acc:
    def __init__(self):
        self.total = 0

    def add_all(self, xs):
        loop_invariant(lambda: self.total >= 0)
        for x in xs:
            self.total += x
        return self.total

print(Acc().add_all([1, 2]))
