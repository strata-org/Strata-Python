# Long inputs: the loops of sort (a shuffled list included), its key scan, tuple.count,
# str.join and str.translate (both of its paths) run in time linear, or n log n, in their size.
l = []
for i in range(5000):
    l.append((5000 - i, i))
l.sort()
print(l[0], l[-1])
f = []
for i in range(3001):
    f.append(float(i % 7))
f.append(float("nan"))
f.sort()
print(f[0], len(f))
print(((0,) * 400000).count(0), ((1,) * 300000 + (2,)).index(2))
s = sorted(range(400000, 0, -1))
print(s[0], s[-1])
print(len("".join(["a"] * 200000)))
print(len(("ab" * 80000).translate({97: "c"})))
print(len(("éb" * 30000).translate({98: None})), len(("ab" * 30000).translate({97: "xy", 98: None})))
m = []
for i in range(20000):
    m.append(((i * 7919) % 101, i))
m.sort()
print(m[0], m[-1])
