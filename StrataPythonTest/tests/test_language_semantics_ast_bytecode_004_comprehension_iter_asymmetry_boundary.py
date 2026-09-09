# NAIVE MODEL WOULD GET WRONG: assumes comprehension body can see class vars
class C:
    items = [1, 2, 3]
    multiplier = 10
    try:
        scaled = [x * multiplier for x in items]  # items OK (outermost iter), multiplier NOT
    except NameError:
        scaled = "NameError"
assert C.scaled == "NameError"
print("BOUNDARY: naive model sees multiplier in class scope; CPython raises NameError in comp body")
