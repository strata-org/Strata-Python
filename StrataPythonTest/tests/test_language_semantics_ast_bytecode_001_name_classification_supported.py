# A program where correct scoping classification matters
x = "global"
def f():
    x = "local"  # LOCAL classification → STORE_FAST
    return x
assert f() == "local"
assert x == "global"  # outer x unchanged
print("OK: name classification correct — local doesn't shadow global")
