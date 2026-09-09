# NAIVE MODEL WOULD GET WRONG: leaks iteration variable (Python 2 behavior)
x = "outer"
_ = [x for x in [1, 2, 3]]
# Naive (no isolation): x = 3. CPython 3.x: x = "outer"
assert x == "outer"
print("BOUNDARY: naive model leaks x=3; CPython isolates comprehension variable")
