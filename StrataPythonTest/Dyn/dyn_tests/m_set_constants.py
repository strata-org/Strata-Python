# Test: set displays of constants, which lower to py.constSet in every position
x = 5
a = {1, 9, 17}
b = {1, 9}
# An element that is not a constant: the set is built as it is.
c = {x, 9, 17}
for y in {1, 9}:
    pass
d = [y for y in {1, -9, 17}]
e = x in {1, 9}
f = x not in {(1, 2), 3.5}
g = 1 < x in {1, 9}
h = x in {1, 9} < 2
k = x in {"a", "b"}
m = {1, 2, 3}
n = {17, 9, 1}
