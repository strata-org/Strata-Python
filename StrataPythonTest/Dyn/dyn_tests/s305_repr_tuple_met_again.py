# Test: a tuple met again through a user __repr__ with a reentrancy flag stops with a gap
class C:
    busy = False
    def __repr__(self):
        if C.busy:
            return "..."
        C.busy = True
        r = "C" + repr(self.t)
        C.busy = False
        return r
c = C()
c.t = (c,)
print(c.t)
