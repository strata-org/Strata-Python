# NAIVE MODEL WOULD GET WRONG: returns try's value, ignoring finally's return
def f():
    try:
        return "try"
    finally:
        return "finally"
# Naive: returns "try". CPython: returns "finally"
assert f() == "finally"
print("BOUNDARY: naive model returns try value; CPython returns finally value")
