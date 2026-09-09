# Multiple assignment: RHS once, targets L→R
log = []
class Logged:
    def __setitem__(self, k, v): log.append((k, v))
d = Logged()
d[0] = d[1] = 42
assert log == [(0, 42), (1, 42)]
print("OK: assignment target order — L→R stores")
