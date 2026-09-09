# Context manager protocol: __exit__ must exist before __enter__ runs
class SafeFile:
    def __init__(self, name): self.name = name
    def __enter__(self): self.data = []; return self
    def __exit__(self, *a): self.data.clear(); return False
sf = SafeFile("test")
with sf as f:
    f.data.append("written")
assert sf.data == []  # cleaned up by __exit__
print("OK: with protocol — __exit__ guaranteed available")
