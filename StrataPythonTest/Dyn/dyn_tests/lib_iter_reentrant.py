# enumerate and reversed read their state after the user code that a step runs, which may have
# stepped or ended the same iterator.

def rest(it):
    out = []
    for x in it:
        out += [x]
    return out



class It:
    def __init__(self):
        self.n = 0
        self.e = None

    def __iter__(self):
        return self

    def __next__(self):
        self.n += 1
        if self.n == 1:
            print(next(self.e))
        if self.n > 4:
            raise StopIteration
        return self.n


it = It()
e = enumerate(it)
it.e = e
print(next(e))
print(next(e))


class Steps:
    def __init__(self):
        self.r = None
        self.calls = 0

    def __len__(self):
        return 4

    def __getitem__(self, i):
        self.calls += 1
        if self.calls == 1:
            print("inner", next(self.r))
        return i


s = Steps()
r = reversed(s)
s.r = r
print(next(r))
print(next(r))
print(rest(r))


class Ends:
    def __init__(self):
        self.r = None
        self.calls = 0

    def __len__(self):
        return 3

    def __getitem__(self, i):
        self.calls += 1
        if self.calls == 1:
            print("inner", rest(self.r))
        return i


s = Ends()
r = reversed(s)
s.r = r
print(next(r))
print(rest(r))


class HintSteps:
    def __init__(self):
        self.r = None
        self.lens = 0
        self.end = False

    def __len__(self):
        self.lens += 1
        if self.lens == 2:
            next(self.r)
        if self.end:
            self.end = False
            rest(self.r)
        return 3

    def __getitem__(self, i):
        return i


s = HintSteps()
r = reversed(s)
s.r = r
print(r.__length_hint__())
s.end = True
print(r.__length_hint__())
print(rest(r))
