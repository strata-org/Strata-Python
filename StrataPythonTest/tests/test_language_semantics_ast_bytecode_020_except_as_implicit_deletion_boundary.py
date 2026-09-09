# NAIVE MODEL WOULD GET WRONG: leaves exception variable bound after handler
def f():
    try:
        raise ValueError("test")
    except ValueError as e:
        captured = str(e)
    # Naive: e still bound. CPython: e deleted
    try:
        return e
    except UnboundLocalError:
        return "deleted"
assert f() == "deleted"
print("BOUNDARY: naive model leaves e bound; CPython deletes it after handler")
