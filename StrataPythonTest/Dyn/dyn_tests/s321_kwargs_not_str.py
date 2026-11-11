# A keyword that isn't a str, a plain value or an object: a Python function raises "keywords must
# be strings"; for a built-in, which error comes first depends on the built-in, so the call stops
# with a gap.
def f(**k):
    return k
try:
    f(**{"q": 1, 1: 2})
except TypeError as e:
    print(e)
class C:
    pass
try:
    f(**{C(): 1})
except TypeError as e:
    print(e)
len(**{"q": 1, 1: 2})
