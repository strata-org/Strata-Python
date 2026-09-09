# Walrus in comprehension assigns to enclosing function scope
def find_first_positive(data):
    positives = [match := x for x in data if x > 0]
    return match if positives else None
assert find_first_positive([-1, -2, 3, 4]) == 4  # last match
print("OK: walrus escape — match visible in enclosing function")
