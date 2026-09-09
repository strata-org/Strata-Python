# NAIVE MODEL WOULD GET WRONG: treats except* like except (first match wins)
import sys
if sys.version_info >= (3, 11):
    exec("""
handled = []
try:
    raise ExceptionGroup("eg", [ValueError(1), TypeError(2)])
except* ValueError as eg:
    handled.append("V")
except* TypeError as eg:
    handled.append("T")
# Naive (first match wins): handled = ["V"]. CPython: both fire
assert handled == ["V", "T"]
print("BOUNDARY: naive first-match model handles one; CPython handles both")
""")
else:
    print("BOUNDARY: except* — skipped (< 3.11)")
