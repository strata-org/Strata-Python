# Test: repr of exceptions, and of a list that contains a tuple that contains the list
print(repr(KeyError("k")), f"{KeyError('k')!s}", ValueError(1, [2]), repr(ValueError()))
a = []
b = (a,)
a += [b]
print(a)
