# yield from delegates and captures return value
def accumulate(values):
    total = 0
    for v in values:
        total += v
        yield total
    return total

def run():
    result = yield from accumulate([1, 2, 3])
    return result

g = run()
vals = []
try:
    while True: vals.append(next(g))
except StopIteration as e:
    final = e.value
assert vals == [1, 3, 6] and final == 6
print("OK: yield from — delegation + return value capture")
