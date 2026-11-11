# One wrong call of each built-in and entry of the library's functions over values and iterables,
# with CPython's message.
class S:
    def __len__(self):
        return 1

    def __getitem__(self, i):
        return i


def wrong(f, *args, **kwargs):
    try:
        f(*args, **kwargs)
    except TypeError as e:
        print(e.args[0])


wrong(hasattr, 1)
wrong(setattr, 1, 2)
wrong(abs)
wrong(hex)
wrong(min, [1], foo=1)
wrong((5).__abs__, 1)
wrong((5).__int__, x=1)
wrong((5).__trunc__, 1)
wrong((1.5).__trunc__, 1)
wrong((1.5).__float__, 1)
wrong(int.__divmod__, 7)
wrong(float.__rdivmod__, 7.0)
wrong(zip().__next__, 1)
wrong(zip().__iter__, 1)
wrong(enumerate([]).__next__, 1)
wrong(reversed(S()).__next__, 1)
wrong(reversed([1]).__next__, 1)
wrong(reversed({1: 2}).__next__, 1)
wrong(reversed([1]).__length_hint__, 1)
wrong(reversed(S()).__length_hint__, 1)
wrong(reversed({1: 2}).__length_hint__, 1)
wrong([].__reversed__, 1)
wrong({}.__reversed__, 1)
wrong(b"".__bytes__, 1)
wrong([].__init__, 1, 2)
wrong(set().__init__, x=1)
wrong({}.__init__, 1, 2)
