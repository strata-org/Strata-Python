# NAIVE MODEL WOULD GET WRONG: evaluates type alias eagerly
import sys
if sys.version_info >= (3, 12):
    exec("""
calls = []
type Lazy = calls.append(1) or int
assert calls == []  # NOT evaluated yet!
_ = Lazy.__value__  # NOW evaluated
assert calls == [1]
print("BOUNDARY: naive model evaluates RHS eagerly; CPython defers to __value__ access")
""")
else:
    print("BOUNDARY: annotation scopes — skipped (< 3.12)")
