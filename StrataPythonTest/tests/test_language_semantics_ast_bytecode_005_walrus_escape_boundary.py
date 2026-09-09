# NAIVE MODEL WOULD GET WRONG: assumes walrus target is local to comprehension
def f():
    [y := x for x in range(5)]
    # Naive: y is local to comprehension, not visible here → NameError
    # CPython: y escapes to f's scope
    return y
assert f() == 4
print("BOUNDARY: naive model says y is comp-local; CPython hoists it to enclosing function")
