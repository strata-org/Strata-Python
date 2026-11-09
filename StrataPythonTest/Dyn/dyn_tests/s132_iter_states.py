# Test: iterator states: a size error and an end that stay, length hints, ranges and empty iterators
d = {1: 2, 3: 4}
it = iter(d)
print(next(it))
d[5] = 6
for k in range(2):
    try:
        next(it)
    except RuntimeError as e:
        print(k, e.args[0])
l = [1]
li = iter(l)
print(next(li), next(li, "end"))
l += [2]
print(next(li, "still end"))
class H:
    def __init__(self, v):
        self.v = v
    def __length_hint__(self):
        return self.v
    def __iter__(self):
        return iter([1, 2])
class BadLen:
    def __len__(self):
        return 1.5
    def __iter__(self):
        return iter([7])
class NegLen:
    def __len__(self):
        return -1
    def __iter__(self):
        return iter([7])
print([*H(NotImplemented)][1], [*BadLen()][0])
for bad in [H(-1), H("x"), NegLen()]:
    try:
        [*bad]
    except (TypeError, ValueError) as e:
        print(type(e).__name__, e.args[0])
r = range(10, 0, -3)
print(len(r), r[0], r[-1], 4 in r, 5 in r, [*r][3])
big = range(2 ** 70, 2 ** 70 + 3)
bi = iter(big)
print(type(bi).__name__, next(bi) - 2 ** 70, len(big))
print(len([*[]]), len([*iter(())]), len({*""}))
a, *b, c = [1, 2]
print(a, len(b), c)
a, *b, c = iter([1, 2, 3])
print(a, b[0], c)
for x in []:
    print("never")
