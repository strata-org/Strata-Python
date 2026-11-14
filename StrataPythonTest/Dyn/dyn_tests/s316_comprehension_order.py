# Comprehensions: the order of iter, next, the element's parts and the hashes, and where an
# exception from each part goes.
log = []

def note(s):
    global log
    log = log + [s]

class It:
    def __init__(self, n):
        self.i = 0
        self.n = n
    def __iter__(self):
        note("iter")
        return self
    def __next__(self):
        self.i += 1
        note("next")
        if self.i > self.n:
            raise StopIteration
        return self.i

class K:
    def __init__(self, v):
        self.v = v
    def __hash__(self):
        note("hash")
        return self.v
    def __eq__(self, other):
        note("eq")
        return self.v == other.v

def key(x):
    note("key")
    return K(x % 2)

def val(x):
    note("val")
    return x

d = {key(x): val(x) for x in It(3)}
print(len(d), [k.v for k in d], [d[k] for k in d], log)
log = []
s = {K(x % 2) for x in It(3)}
print(len(s), log)
log = []
print([(a, b) for a in It(2) for b in It(a) if a != b], log)

def stop():
    raise StopIteration
try:
    [stop() for x in range(3)]
except StopIteration:
    print("StopIteration from the element")

class BadIter:
    def __iter__(self):
        return self
    def __next__(self):
        raise ValueError("next")
try:
    [x for x in BadIter()]
except ValueError as e:
    print("ValueError", e)
try:
    {x: 1 for x in [[1]]}
except TypeError as e:
    print("TypeError", e)
try:
    [x for x in 3]
except TypeError as e:
    print("TypeError", e)
