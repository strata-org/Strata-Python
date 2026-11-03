# sum: the int, float and generic phases, the start, and the argument errors.
class I(int):
    pass


class F(float):
    pass


class S(str):
    pass


class Acc:
    def __add__(self, other):
        print("add", other)
        return self

    def __radd__(self, other):
        print("radd", other)
        return self


class Countdown:
    def __init__(self, n):
        self.n = n

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        return self.n


print(sum([]), sum([], 5), sum([1, 2, 3]), sum(range(101)), sum([True, True, 2]))
print(sum([0.1] * 10))
print(sum([2 ** 63, -2 ** 63] + [0.1] * 10))
print(sum([1, 2.5, 3]), sum([1.5, 2, True]), sum([0.5, 2 ** 64]))
print(sum([2 ** 62, 2 ** 62, 1]), sum([2 ** 64, 1]), sum([1], 2 ** 70))
print(sum([1e308 * 10, 1.0]), sum([1e308, 1e308]), sum([1e308, 1e308, -1e308]))
print(sum([-0.0]), sum([-0.0], -0.0), sum([], -0.0))
l = sum([[1], [2, 3]], [])
t = sum(((1,), (2,)), ())
print(len(l), l[0], l[2], len(t), t[1])
print(sum([1, 2], start=10), sum([1, 2], 0.5))
a = Acc()
print(sum([a, 1, 2.5]) is a)
print(sum([1, 2.0, a, 3]) is a)
print(sum(Countdown(4)), sum(Countdown(3), 0.5))
three, four = 3, 4
print(sum({1: "a", 2: "b"}), sum({three, four}))
for start in ["", b"x"]:
    try:
        sum([], start)
    except TypeError as e:
        print(e.args[0])
for args, kwargs in [((), {}), (([1], 2, 3), {}), (([1],), {"begin": 3}), ((5,), {})]:
    try:
        sum(*args, **kwargs)
    except TypeError as e:
        print(e.args[0])
try:
    sum([1, "a"])
except TypeError as e:
    print(e.args[0])
try:
    sum(["a"], "")
except TypeError as e:
    print(e.args[0])
# The subclasses of int, float and str need their constructors, which come with the constructors
# of the built-in types.
print(sum([I(5), 1]), sum([1.0, I(2)]), sum([F(1.5), 1]), sum([1.0, F(0.25)]))
try:
    sum([], S("a"))
except TypeError as e:
    print(e.args[0])
