# The methods of list (but sort), tuple and range: in-place changes, argument errors, the
# searches with a user __eq__ (which may grow the list), and the arithmetic of range.
class E:
    def __init__(self, v, log):
        self.v = v
        self.log = log

    def __eq__(self, other):
        print("eq", self.v)
        if self.log is not None and len(self.log) < 5:
            self.log.append(99)
        return self.v == other

    def __repr__(self):
        return f"E({self.v})"


class I:
    def __index__(self):
        print("index")
        return 1


class It:
    def __iter__(self):
        print("iter")
        return iter([7, 8])


def show(f, *args):
    try:
        print(repr(f(*args)))
    except (TypeError, ValueError, IndexError, OverflowError) as e:
        print(type(e).__name__, e.args[0])


l = [1, 2, 3]
l.append(4)
l.insert(0, 0)
l.insert(-1, 9)
l.insert(100, 5)
l.insert(I(), "i")
print(l, l.pop(), l.pop(0), l.pop(I()), l)
show(l.pop, 100)
show([].pop)
show(l.pop, "x")
show(l.insert, 2 ** 70, 0)
c = l.copy()
c.reverse()
print(c, l)
l.extend([10, 11])
l.extend((12,))
l.extend(It())
l.extend(l)
print(l)
show(l.extend, 5)
l.clear()
print(l)
m = [1, 2, 1, 3, 1]
print(m.count(1), m.index(3), m.index(1, 1), m.index(1, -2), m.index(1, I()))
show(m.index, 7)
show(m.index, 1, None)
show(m.index, E(4, None))
m.remove(1)
print(m)
show(m.remove, 42)
log = [1, 2]
print(log.count(E(5, log)), len(log))
g = [1, 2, 3]
print(g.index(E(3, None)))
g.remove(E(2, None))
print(g)
t = (1, 2, 1, "a")
print(t.count(1), t.index("a"), t.index(1, 1), t.count(E(1, None)))
show(t.index, 5)
show(t.index, 1, 3)
r = range(0, 20, 3)
print(r.count(9), r.count(10), r.index(9), r.count(True), r.index(False))
show(r.index, 10)
print(r.count(E(6, None)), r.index(E(3, None)))
show(r.index, E(5, None))
print(list.count([1, 1], 1), tuple.index((5, 6), 6))


class Refill:
    def __index__(self):
        lr[:] = [7, 8, 9, 10]
        return -1


lr = [1]
print(lr.pop(Refill()), lr)


class Grow:
    def __index__(self):
        lg.append(4)
        return 3


lg = [1, 2, 3]
lg.insert(Grow(), 9)
print(lg)
show(list.extend, zip([1]), [2])
show(list.append, (1,), 2)
print(range(0, 5).index(4))
show(range(0).index, True)
show(range(3).index, "x")


class L(list):
    def __iter__(self):
        return iter([9])


x = L([1])
x.extend(x)
print(list.__repr__(x))
y = L([1, 2])
y.__init__(y)
print(list.__repr__(y))


class R:
    def __eq__(self, other):
        lr.clear()
        return True


lr = [R(), 1, 2]
print(lr.remove(7), lr)


class T:
    def __eq__(self, other):
        del lt[0]
        return True


lt = [0, 0, 0, T()]
print(lt.remove(5), len(lt))
