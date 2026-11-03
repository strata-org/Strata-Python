# zip and enumerate: lazy iterators, zip(strict=True), enumerate(start=), and the argument errors.
def count(it):
    n = 0
    for _ in it:
        n += 1
    return n


class Again:
    def __init__(self):
        self.calls = 0

    def __iter__(self):
        return self

    def __next__(self):
        self.calls += 1
        if self.calls == 1:
            return 1
        if self.calls in (3, 4):
            return self.calls
        raise StopIteration


class Logged:
    def __index__(self):
        print("start")
        return 5


class LoudIter:
    def __iter__(self):
        print("iter")
        return iter([7])


def show(it):
    for x in it:
        print(x[0], x[1])


show(zip([1, 2, 3], "ab"))
show(enumerate("xy"))
show(enumerate("xy", 10))
show(enumerate("z", start=-3))
show(enumerate("z", 10 ** 20))
show(enumerate(LoudIter(), Logged()))
z = zip([1, 2], [3])
print(next(z)[1], next(z, "end"))
print(count(zip()), count(zip([])))
a = Again()
z = zip(a)
for _ in range(3):
    print(count(z))
e = enumerate(Again())
for _ in range(3):
    print(count(e))
it = iter([1, 2, 3])
z = zip(it, it)
print(next(z)[1])
print(type(zip()).__name__, type(enumerate([])).__name__, iter(z) is z)
for args, kwargs in [(([1, 2], [3]), {"strict": True}), (([1], [3, 4], [5, 6]), {"strict": True}),
                     (([1, 2], [3, 4], [5]), {"strict": True})]:
    try:
        count(zip(*args, **kwargs))
    except ValueError as e:
        print(e.args[0])
print(count(zip([1], [2], strict=True)))
for f, args, kwargs in [(zip, (5,), {}), (zip, ([],), {"x": 1}), (zip, ([],), {"strict": True, "x": 1}),
                        (enumerate, ([], 1, 2), {}), (enumerate, ([],), {"start": "a"}),
                        (enumerate, (5,), {}),
                        # The message of a wrong keyword depends on the call path: a gap.
                        (enumerate, ([],), {"x": 1})]:
    try:
        f(*args, **kwargs)
    except TypeError as e:
        print(e.args[0])
