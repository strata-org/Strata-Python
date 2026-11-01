# Test: print raises TypeError for a sep that is not a str, after nothing is written
print("before")
print(1, sep=3)
