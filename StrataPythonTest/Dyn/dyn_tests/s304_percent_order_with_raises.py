# Test: a literal % with a tuple display: the first item's str raises before the second item runs
class A:
    def __str__(self):
        raise KeyError("from str")
def g():
    raise ValueError("from g")
try:
    x = '%s %s' % (A(), g())
except ValueError:
    print("g raised first")
except KeyError:
    print("str raised first")
