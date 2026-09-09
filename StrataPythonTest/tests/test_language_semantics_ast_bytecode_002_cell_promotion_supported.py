# A program relying on cell sharing between parent and child
def counter():
    n = 0  # promoted to CELL because inner captures it
    def inc():
        nonlocal n
        n += 1
        return n
    return inc
c = counter()
assert c() == 1
assert c() == 2
assert c() == 3
print("OK: cell promotion — shared mutable state via closure")
