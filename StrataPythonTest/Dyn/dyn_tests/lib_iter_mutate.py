# any, all, sum, max and min where user code changes the container in the middle of the call.
l = [0, 0, 0]


class Grow:
    def __bool__(self):
        if len(l) < 5:
            l[len(l):] = [Grow()]
        return len(l) == 5 and self is l[4]


l[0] = Grow()
l[1] = Grow()
l[2] = Grow()
print(any(l), len(l))

m = []


class Clear:
    def __bool__(self):
        del m[:]
        return True


m += [Clear()]
m += [0]
print(all(m), len(m))

d = {1: 0, 2: 0}


def addkey(k):
    d[k + 10] = 0
    return k


try:
    max(d, key=addkey)
except RuntimeError as e:
    print(e.args[0])

n = [1, 2]


class Ext:
    def __radd__(self, other):
        n[len(n):] = [30, 40]
        return other + 25


n += [Ext()]
print(sum(n))

q = []


class Q:
    def __init__(self, v):
        self.v = v

    def __gt__(self, other):
        print("gt", self.v, other.v)
        if q:
            del q[-1]
        return self.v > other.v


q += [Q(1), Q(5), Q(4), Q(3), Q(2)]
r = max(q)
print(r.v, len(q))

it = iter([0, 1, 0, 1, 0])
seen = []


class Skip:
    def __init__(self, v):
        self.v = v

    def __bool__(self):
        seen[len(seen):] = [self.v]
        next(it, None)
        return False


it = iter([Skip(0), Skip(1), Skip(2), Skip(3), Skip(4)])
print(any(it), len(seen), seen[0], seen[1], seen[2])

# set.update comes with the set methods.
s = {1, 2}


def addmember(x):
    s.update({x + 10})
    return x


try:
    min(s, key=addmember)
except RuntimeError as e:
    print(e.args[0])
