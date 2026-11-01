# Test: print with sep and end, and the values whose str runs no protocol
print()
print(1, 2, 3)
print(1, 2, sep="-")
print("a", "b", sep="", end="!\n")
print(None, True, False, 1.5, -0.0, 10**20, "x")
print("no newline", end="")
print(sep=None, end=None)
print(**{"sep": "+"}, end="|\n")
