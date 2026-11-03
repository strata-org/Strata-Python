# Test: the subclass of OSError that each errno from 0 to 199 selects
names = []
i = 0
while i < 200:
    names += [type(OSError(i, "x")).__name__]
    i = i + 1
