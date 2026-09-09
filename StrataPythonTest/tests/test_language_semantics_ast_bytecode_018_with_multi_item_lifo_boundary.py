# NAIVE MODEL WOULD GET WRONG: exits in entry order (FIFO)
order = []
class CM:
    def __init__(self, n): self.n = n
    def __enter__(self): order.append(f"+{self.n}"); return self
    def __exit__(self, *a): order.append(f"-{self.n}"); return False
with CM(1), CM(2), CM(3):
    pass
# Naive FIFO exit: [+1,+2,+3,-1,-2,-3]. CPython LIFO: [+1,+2,+3,-3,-2,-1]
assert order == ["+1", "+2", "+3", "-3", "-2", "-1"]
print("BOUNDARY: naive FIFO exit order; CPython uses LIFO")
