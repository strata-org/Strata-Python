# NAIVE MODEL WOULD GET WRONG: uses == for None/True/False matching
import sys
if sys.version_info >= (3, 10):
    exec("""
class Tricky:
    def __eq__(self, other): return True  # equals everything
t = Tricky()
match t:
    case None: result = "None"
    case _: result = "other"
# Naive (uses ==): Tricky().__eq__(None) is True → matches None
# CPython: uses 'is' for singletons → doesn't match
assert result == "other"
print("BOUNDARY: naive == matching hits Tricky.__eq__; CPython uses 'is' for None")
""")
else:
    print("BOUNDARY: pattern matching — skipped (< 3.10)")
