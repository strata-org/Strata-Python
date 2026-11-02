# Test: the dunders of str, bytes, tuple, list, dict and set called directly
N = NotImplemented
print([1].__eq__((1,)) is N, "a".__lt__(1) is N, [1].__iadd__((2,)) == [1, 2], [1].__imul__(2) == [1, 1])
print("a".__rmul__(2), (1,).__hash__() == (1,).__hash__(), [1].__contains__(1), (1, 2).__len__())
print({1: 2}.__getitem__(1), {1: 2}.__or__([1]) is N, {1: 2}.__ror__({3: 4}) == {3: 4, 1: 2}, {}.__eq__([]) is N)
print({}.__lt__({}) is N, {1}.__or__([1]) is N, {1}.__rsub__({1, 2}) == {2}, {1}.__le__({1, 2}))
print({1}.__ior__([2]) is N, {1, 2}.__iand__({2}) == {2})
print([1].__setitem__(0, 5), [1].__delitem__(0))
print([1].__lt__([2]), (1,).__ge__((1,)), "ab".__add__("c"), b"a".__add__(b"b") == b"ab", (1,).__add__((2,)) == (1, 2))
print({1: 2}.__ior__({3: 4}) == {1: 2, 3: 4}, {1: 2}.__len__(), {1}.__xor__({2}) == {1, 2})
print({1}.__ror__({2}) == {1, 2}, "abc".__getitem__(1))
print([1, 2, 3].__getitem__(-1), b"ab".__contains__(98), "abc".__contains__("bc"), (2,).__mul__(2) == (2, 2))
print("a".__add__(1))
