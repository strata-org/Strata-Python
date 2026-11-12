# A set subclass looked up in a set: CPython 3.12 retries the lookup with a frozenset.
class S(set):
    pass


try:
    print(S([5]) in set([frozenset([5])]))
except TypeError as e:
    print("TypeError", e)
