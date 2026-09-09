# Multiple context managers: LIFO cleanup order
order = []
class CM:
    def __init__(self, n): self.n = n
    def __enter__(self): order.append(f"+{self.n}"); return self
    def __exit__(self, *a): order.append(f"-{self.n}"); return False
with CM(1), CM(2), CM(3): pass
assert order == ["+1", "+2", "+3", "-3", "-2", "-1"]
print("OK: with multi-item — LIFO exit order")
