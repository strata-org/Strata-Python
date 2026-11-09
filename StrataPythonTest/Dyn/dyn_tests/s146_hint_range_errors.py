# Test: length hints out of a Py_ssize_t's range raise OverflowError before the sign check, and hints up to the model's bound are used
class H:
    def __init__(self, v):
        self.v = v
    def __iter__(self):
        return iter([1])
    def __length_hint__(self):
        return self.v
for v in [2**63, -2**63, -2**63 - 1, -1, 2**20]:
    try:
        print(len([*H(v)]))
    except (OverflowError, ValueError, MemoryError) as e:
        print(type(e).__name__, e.args[0] if e.args else "")
