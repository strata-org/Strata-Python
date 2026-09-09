# NAIVE MODEL WOULD GET WRONG: assumes class body shares function locals
def f():
    secret = 42
    class C:
        try:
            val = secret  # class body can see enclosing function via ClassDeref
        except NameError:
            val = "hidden"
    return C.val
# This one actually works in CPython (ClassDeref). The boundary is:
# a naive model that treats class body as plain nested scope would get
# the STORE semantics wrong (class vars use STORE_NAME, not STORE_FAST)
result = f()
assert result == 42
print("BOUNDARY: class body uses STORE_NAME (dict-based), not STORE_FAST")
