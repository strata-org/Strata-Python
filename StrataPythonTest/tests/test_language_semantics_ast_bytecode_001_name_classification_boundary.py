# NAIVE MODEL WOULD GET WRONG: assumes x is global because it's used before assignment
# A naive "resolve at use site" model would find x in globals. CPython says: LOCAL everywhere.
x = "global"
def f():
    try:
        print(x)  # Naive: prints "global". CPython: UnboundLocalError
    except UnboundLocalError as e:
        print(f"CORRECT: {e}")
        return "unbound"
    x = "local"
    return "wrong"
assert f() == "unbound"
print("BOUNDARY: naive model would resolve x globally; CPython raises UnboundLocalError")
