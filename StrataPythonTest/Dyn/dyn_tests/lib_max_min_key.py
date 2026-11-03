# max and min with a key that is itself a looping built-in over a user iterable: the key call
# suspends and resumes across activations.
class Countdown:
    def __init__(self, n):
        self.n = n

    def __iter__(self):
        return Down(self.n)


class Down:
    def __init__(self, n):
        self.n = n

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        return self.n


class Caller:
    __call__ = staticmethod(sum)


class Keys:
    def total(self, x):
        return sum(x)


rows = [Countdown(3), Countdown(5), Countdown(2)]
print(max(rows, key=sum).n, min(rows, key=sum).n)
print(max(rows, key=any).n, min(rows, key=all).n, max(rows, key=max).n)
print(max(rows, key=Caller()).n, min(rows, key=Keys().total).n)
print(max([Countdown(4), Countdown(40), Countdown(7)], key=sum).n)
