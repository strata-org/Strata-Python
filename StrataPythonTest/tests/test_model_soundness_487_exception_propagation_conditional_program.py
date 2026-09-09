# Witness: a raising operation INSIDE an if-body, not at
# expression-statement level. CPython raises ZeroDivisionError.
# Strata:  misses it as well -- the exception check does not descend into
#          if/while/for bodies (raise/exception-as-value, laurel 274, 385).
x: int = 1
y: int = 0
if x == 1:
    z: int = x // y   # CPython: ZeroDivisionError; Strata misses it
