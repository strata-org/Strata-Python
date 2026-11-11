# The operations reach the dict views' own dunders: len and bool through __len__, in through
# __contains__, and the comparisons and set operators in both orders, with NotImplemented where
# CPython's slots give it.
d = {1: 10, 2: 20}
e = {2: 20, 3: 30}
k, i, v = d.keys(), d.items(), d.values()
print(len(k), len(i), len(v), bool({}.keys()), bool(v))
print(1 in k, 3 in k, 1 not in k, (1, 10) in i, (1, 20) in i, [1] in i)
print(k == set([1, 2]), k != set([1, 2]), k < set([1, 2, 3]), k <= set([1, 2]), k > set([1]), k >= set([3]))
print(k == [1, 2], i == set([(1, 10), (2, 20)]), k == e.keys(), set([1, 2]) == k)
print(sorted(k & set([2, 3])), sorted(set([2, 3]) & k), sorted(k | set([5])), sorted(set([5]) | k))
print(sorted(k - set([1])), sorted(set([1, 9]) - k), sorted(k ^ e.keys()), sorted(i ^ e.items()))
print(sorted(k & e.keys()), sorted(i - e.items()), k.isdisjoint(set([7])), i.isdisjoint(e.items()))
