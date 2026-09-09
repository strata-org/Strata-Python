# NAIVE MODEL WOULD GET WRONG: assumes nested function can see class variables
class C:
    x = 10
    def get_x(self):
        # Naive LEGB model: x found in "enclosing" class scope → returns 10
        # CPython: class scope skipped → NameError
        try:
            return x
        except NameError:
            return "NameError"
assert C().get_x() == "NameError"
print("BOUNDARY: naive LEGB gives 10; CPython raises NameError (class scope opaque)")
