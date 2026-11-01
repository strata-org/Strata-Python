# Test: print raises TypeError for an unknown keyword before it checks sep
print(1, sep=3, bad=1)
