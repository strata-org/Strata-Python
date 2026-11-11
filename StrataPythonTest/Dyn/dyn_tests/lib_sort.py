# list.sort and sorted: the key calls, reverse, CPython's choice of comparison (a type's own
# __lt__ first, tuples by their first members that differ), a list changed during the sort,
# failing keys and comparisons, and the argument errors.
class A:
    def __init__(self, v):
        self.v = v

    def __lt__(self, other):
        print("lt", self.v, other.v)
        return NotImplemented

    def __gt__(self, other):
        print("gt", self.v, other.v)
        return self.v > other.v

    def __repr__(self):
        return f"A({self.v})"


class B:
    def __init__(self, v):
        self.v = v

    def __lt__(self, other):
        print("blt", self.v, other.v)
        return self.v < other.v

    def __eq__(self, other):
        print("beq", self.v, other.v)
        return self.v == other.v

    def __repr__(self):
        return f"B({self.v})"


def show(f, *args, **kwargs):
    try:
        print(repr(f(*args, **kwargs)))
    except (TypeError, ValueError, ZeroDivisionError) as e:
        print(type(e).__name__, e.args[0])


l = [3, 1, 2]
l.sort()
print(l)
l.sort(reverse=True)
print(l)
print(sorted(["b", "a", "c"]), sorted([2.5, 1, True, -3]), sorted([]), sorted((5,)))
print(sorted(["bb", "a", "ccc"], key=len), sorted(["bb", "a", "cc"], key=len, reverse=True))
print(sorted([A(2), A(1)]))
print(sorted([B(3), B(1), B(2)]))
print(sorted([(1, B(2)), (1, B(1)), (0, B(5))]))
print(sorted([(B(1), 2), (B(1), 1)]))
print(sorted([[2], [1, 0], [1]]))
print(sorted(iter([3, 2, 1])), sorted({"k": 1, "j": 2}), sorted(range(3), key=lambda x: -x))


def key(x):
    print("key", x)
    return -x


print(sorted([1, 2, 3], key=key))
show(sorted, [1, "a", 2])
show(sorted, [1, 0], key=lambda x: 1 // x)
m = [3, 1, 2]


def grow(x):
    m.append(x)
    return x


show(m.sort, key=grow)
print(m)
n = [3, 1, 2]


def peek(x):
    print("len during sort", len(n))
    return x


n.sort(key=peek)
print(n)
show([2, 1].sort, 1)
show([2, 1].sort, foo=1)
show([2, 1].sort, key=5)
show(sorted)
show(sorted, [1], [2])
show(sorted, 5)
show(sorted, [2, 1], foo=1)
print(sorted([1, 2], reverse=1.5), sorted([(2, "x"), (1, "y")], key=lambda t: t[1]))


class Rows:
    def __init__(self, xs):
        self.xs = xs

    def __iter__(self):
        return iter(self.xs)


for r in sorted([Rows([2, 1]), Rows([1, 5]), Rows([1])], key=list):
    print(r.xs)


class Group(list):
    def __new__(cls, *args):
        print("new")
        return super().__new__(cls)


print(sorted([[3], [1, 2], [2]], key=Group))


class Caller:
    __call__ = staticmethod(list)


class Flip:
    def __init__(self, xs):
        self.xs = xs

    def __iter__(self):
        Caller.__call__ = staticmethod(tuple)
        return iter(self.xs)


show(sorted, [Flip([2]), Flip([1]), Flip([0])], key=Caller())
k1 = [3, 1, 2]


def churn(x):
    k1.append(0)
    k1.pop()
    return x


show(k1.sort, key=churn)
k2 = [3, 1, 2]


def quiet(x):
    k2.extend(iter([]))
    k2.sort()
    return x


k2.sort(key=quiet)
print(k2)
inf = float("inf")
print(sorted([0.0, -0.0, 0, False, -inf, inf, 2 ** 1000, 1e300, -2 ** 1000, 1.5, 3]))
print(sorted(["é", "e", "z", "", "ab", "a", "😀", "Z"]), sorted(["b", "a"], reverse=True))
print(sorted([1, 1.0, True, 1], reverse=True), sorted([float("nan"), 1.0, 0.5]))


class Late:
    count = 0

    def __init__(self, v):
        self.v = v

    def __lt__(self, other):
        Late.count += 1
        if Late.count == Late.stop:
            raise ValueError("late")
        return self.v < other.v


def late_sort(stop, reverse):
    Late.count = 0
    Late.stop = stop
    items = []
    for i in range(300):
        items.append(Late((i * 7919) % 300))
    try:
        items.sort(reverse=reverse)
    except ValueError:
        pass
    vs = []
    for x in items:
        vs.append(x.v)
    print(stop, reverse, vs)


late_sort(400, False)
late_sort(1500, False)
late_sort(1500, True)
