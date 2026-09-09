# Structural pattern matching (3.10+)
import sys
if sys.version_info >= (3, 10):
    exec("""
def classify(point):
    match point:
        case (0, 0): return "origin"
        case (x, 0): return f"x-axis at {x}"
        case (0, y): return f"y-axis at {y}"
        case (x, y): return f"({x}, {y})"
assert classify((0,0)) == "origin"
assert classify((3,0)) == "x-axis at 3"
assert classify((1,2)) == "(1, 2)"
print("OK: pattern matching — structural decomposition")
""")
else:
    print("OK: pattern matching — skipped (< 3.10)")
