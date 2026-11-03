# any and all: the first decisive item ends the walk; user __bool__, __len__ and iterators.
class Loud:
    def __init__(self, v):
        self.v = v

    def __bool__(self):
        print("bool", self.v)
        return self.v


class Sized:
    def __len__(self):
        return 0


class Countdown:
    def __init__(self, n):
        self.n = n

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        print("next", self.n)
        return self.n


class Bad:
    def __bool__(self):
        return 1


class Raises:
    def __iter__(self):
        return self

    def __next__(self):
        raise ValueError("boom")


print(any([]), all([]))
print(any([0, "", None, 3]), all([1, "a", 0, 2]))
print(any([Loud(False), Loud(True), Loud(True)]))
print(all([Loud(True), Loud(False), Loud(True)]))
print(any([Sized()]), all([Sized()]))
print(any(range(0)), all(range(1, 5)), any(range(3)))
print(any({0: 1}), all({1: 0, 2: 0}), any(""), all("ab"), any((0, 0.0)))
it = Countdown(4)
print(any(it))
print(next(it))
print(all(Countdown(3)))
print(any(Countdown(0)), all(Countdown(0)))
for args in [(), (1, 2)]:
    try:
        any(*args)
    except TypeError as e:
        print(e.args[0])
try:
    all(5)
except TypeError as e:
    print(e.args[0])
try:
    any(x=[1])
except TypeError as e:
    print(e.args[0])
try:
    any([Bad()])
except TypeError as e:
    print(e.args[0])
try:
    all(Raises())
except ValueError as e:
    print(e.args[0])
