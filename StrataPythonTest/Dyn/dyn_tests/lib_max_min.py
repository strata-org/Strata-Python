# max and min: one iterable or several arguments, key=, default=, the first of equal items wins.
class A:
    def __init__(self, v):
        self.v = v

    def __gt__(self, other):
        print("gt", self.v, other.v)
        return self.v > other.v

    def __lt__(self, other):
        print("lt", self.v, other.v)
        return self.v < other.v


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


def neg(x):
    print("key", x)
    return -x


print(max([3, 1, 2]), min([3, 1, 2]), max(3, 1, 2), min(3, 1, 2), max("ba"), min((2.5, 1)))
print(max([A(1), A(3), A(2)]).v)
print(min([A(2), A(1), A(3)]).v)
print(max([1, 3, 2], key=neg), min(3, 1, 2, key=neg))
print(max([], default=7), min([], default=None), max([5], default=7), max([1, 2], key=None))
print(max((1, 1.0)), min((1.0, 1)), max([0, False]), min([True, 1]))
print(max(Countdown(5)), min(Countdown(4), key=neg))
five, three, eight = 5, 3, 8
print(max({2: "a", 9: "b", 4: "c"}), min({five, three, eight}))
for args, kwargs in [((), {}), (([],), {}), ((1, 2), {"default": 0}), (([1],), {"foo": 1}),
                     ((1,), {}), (([1],), {"key": None, "default": 1, "foo": 2})]:
    try:
        max(*args, **kwargs)
    except (TypeError, ValueError) as e:
        print(type(e).__name__, e.args[0])
try:
    min([], key=neg)
except ValueError as e:
    print(e.args[0])
try:
    max([1, "a"])
except TypeError as e:
    print(e.args[0])
try:
    min([1, 2], key=len)
except TypeError as e:
    print(e.args[0])
