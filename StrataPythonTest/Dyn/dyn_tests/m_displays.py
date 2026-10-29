# Displays build as CPython builds them.  Before the first `*x`, the elements are one
# `BUILD_LIST`/`BUILD_SET`; then each `*x` extends and each later element is appended.  A
# tuple with a `*x` is a list, then `listToTuple`.  A dict is runs of pairs, key first, and
# `dictUpdate` (last wins) for each `**d`.  Building a set or dict raises for an
# unhashable element or key.
t0 = ()
t1 = (a,)
t2 = (a, b)
t3 = (a, *xs, b, c)
l0 = []
l1 = [a, b]
l2 = [*xs]
l3 = [a, *xs, b, *ys]
s1 = {a, b}
s2 = {a, *xs, b}
d0 = {}
d1 = {"k": a, b: c}
d2 = {**d}
d3 = {"p": a, **d, "q": b, "r": c, **e}
n = [(a, *xs), {b: [c]}]
# CPython cuts a dict run into chunks of 17 pairs, and builds a chunk of more than 15 pairs,
# or a set of more than 30 elements, one element at a time, hashing each as it is evaluated.
d15 = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 11: 11, 12: 12, 13: 13, 14: 14}
d16 = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 11: 11, 12: 12, 13: 13, 14: 14, 15: 15}
s30 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29}
s31 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
d19 = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 11: 11, 12: 12, 13: 13, 14: 14, 15: 15, 16: 16, 17: 17, 18: 18}
d17 = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 11: 11, 12: 12, 13: 13, 14: 14, 15: 15, 16: 16}
d17u = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 10: 10, 11: 11, 12: 12, 13: 13, 14: 14, 15: 15, 16: 16, **d}
