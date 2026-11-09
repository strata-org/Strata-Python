# Test: the argument errors of range, len, iter and next
tests = [
    lambda: range(),
    lambda: range(1, 2, 3, 4),
    lambda: range(1, x=2),
    lambda: range("a"),
    lambda: range(1, "b"),
    lambda: range(1, 2, "c"),
    lambda: range(1, 2, 0),
    lambda: len(),
    lambda: len(1, 2),
    lambda: len(x=1),
    lambda: iter(),
    lambda: iter(1, 2, 3),
    lambda: iter([], x=1),
    lambda: next(),
    lambda: next(1, 2, 3),
    lambda: next(iter([]), x=1),
    lambda: next(iter([])),
    lambda: next(5),
    lambda: next(5, 6),
    lambda: iter(5, 6),
    lambda: len(iter([])),
    lambda: range(1.0),
    lambda: range(True, 3)[0],
]
for t in tests:
    try:
        r = t()
        print("ok", type(r).__name__)
    except Exception as e:
        print(type(e).__name__, e.args[0])
