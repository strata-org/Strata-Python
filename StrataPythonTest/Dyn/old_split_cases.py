# The invariants whose old parts StrataPythonTestExtra/DynOldSplitTest.lean pins, one per line;
# never run.
e = all(v > 0 for v in tables[len(OLD(xs))].values())
e = all(True for x in OLD(xs))
e = all(True for k, v in OLD(d).items())
e = OLD(d).items()
e = OLD(d).values()
e = OLD(t)[OLD(i)].items()
e = all(v > 0 for v in OLD(t)[OLD(i)].values())
e = len(OLD(xs)) == len(xs) + 1
e = OLD(xs) == xs
e = all(x > 0 for x in OLD(xs))
e = all(v > 0 for k, v in OLD(d).items())
e = len(xs[OLD(a):]) >= 0
e = len(xs[OLD(a):OLD(b)]) >= 0
e = len(OLD(xs)[OLD(a):]) >= 0
e = isinstance(OLD(x), int)
e = allocated == OLD(allocated) + 1
e = all(OLD(y) > 0 for y in ys)
e = (OLD(a) if OLD(b) else 0) >= 0
e = -(OLD(a) + n) <= 0
e = all(True for x in OLD(xs) if x)
e = any(OLD(a) + 1 for x in xs)
e = OLD(d).items
e = all(x > 0 for x in xs if OLD(n) > 0)
e = all(any(True for y in OLD(ys)) for x in OLD(xs))
e = all(OLD(x) for x in OLD(xs))
e = OLD(a) > 0 and x > 0
e = not OLD(b)
e = 0 < OLD(a) < n
e = OLD(a) > 0 or OLD(b) > 0
