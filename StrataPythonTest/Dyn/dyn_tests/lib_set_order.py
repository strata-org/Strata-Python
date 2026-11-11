# The order of the sets that the set methods build, as CPython's tables give it: a difference
# walks the set, a difference_update trims once per argument, a symmetric difference starts from
# its argument, and pop scans from the table's finger.
print(list(set([8, 1, 2, 3]).difference([2, 3])))
s = set([*range(10), 18, 26])
s.difference_update(range(8), [8])
print(list(s))
t = set()
t.symmetric_difference_update(dict.fromkeys([11, 3]))
print(list(t), list(set().symmetric_difference(set([11, 3]))))
b = set([8, 1, 2, 3])
b.difference_update([2, 3])
print(list(b))
c = set([8, 1, 2, 3])
try:
    c.difference_update([2, 3, []])
except TypeError as e:
    print(e)
print(list(c))
print(list(set(dict.fromkeys([17, 1, 2, 3, 4]))))
p = set([1, 2, 3])
p.pop()
p.add(1)
print(p.pop())
print(list(set([17, 1]).union([33, 2])), list(set([17, 1, 33]).intersection([33, 17])))
