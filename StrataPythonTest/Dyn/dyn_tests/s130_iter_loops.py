# Test: [*x], {*x}, a, *b = x, f(*x) and x in y over user iterators and __getitem__ objects, with CPython's calls and errors
class It:
    def __init__(self, n):
        self.i = 0
        self.n = n
    def __iter__(self):
        print("iter")
        return self
    def __next__(self):
        if self.i >= self.n:
            raise StopIteration
        self.i += 1
        print("next", self.i)
        return self.i
    def __length_hint__(self):
        print("hint")
        return 2
class G:
    def __getitem__(self, i):
        if i >= 3:
            raise IndexError
        return i
def show(xs):
    print(len(xs), *xs)
show([*It(3)])
show({*It(2)})
a, *b, c = It(4)
print(a, len(b), b[0], b[1], c)
def f(*args):
    return args
t = f(*It(2))
print(len(t), t[0], t[1])
print(2 in It(3), 5 in It(2), 1 in G(), 7 in G())
show([*G()])
show([*{4: 0}])
try:
    a, *b, c = It(1)
except ValueError as e:
    print(e.args[0])
try:
    [*5]
except TypeError as e:
    print(e.args[0])
try:
    print(*5)
except TypeError as e:
    print(e.args[0])
try:
    a, *b = 5
except TypeError as e:
    print(e.args[0])
try:
    1 in 5
except TypeError as e:
    print(e.args[0])
