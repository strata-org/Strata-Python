# A list comprehension and a generator expression side by side.
def f(xs, y):
    a = [x + y for x in xs]
    b = (x * y for x in xs)
    return a, b
