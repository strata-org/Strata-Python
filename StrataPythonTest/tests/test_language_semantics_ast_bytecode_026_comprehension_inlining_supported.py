# Comprehension doesn't leak iteration variable
x = "safe"
squares = [x*x for x in range(5)]
assert x == "safe" and squares == [0, 1, 4, 9, 16]
print("OK: comprehension inlining — variable isolated")
