# any, all, max, min and sum over a set of strs, whose order depends on the hash seed, give the
# results that every order gives.
a, b, c, p, q, e = "a", "b", "c", "p", "q", ""
one, two, big = 1, 2, 2 ** 70
print(any({a, b}), all({e, b}), max({a, b, c}), min({q, p}), sum({one, two, big}), sum({one, two}, 5))
try:
    sum({a, b})
except TypeError as x:
    print(x.args[0])
print(max({a, b}, key=None))
# A set of ints whose order depends on the seed: a str placed in it, then removed.
ints = {a, 1, 2, 2 ** 70, -5} - {a}
print(sum(ints), sum(ints, 5), max(ints), min(ints), any(ints), all(ints), max(ints, default=0))
print(any({a} - {a}), all({a} - {a}), sum({a} - {a}))
