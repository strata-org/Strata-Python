# except* handles multiple exception types from a group
import sys
if sys.version_info >= (3, 11):
    exec("""
errors = []
try:
    raise ExceptionGroup("batch", [ValueError("bad"), TypeError("wrong")])
except* ValueError as eg:
    errors.extend(eg.exceptions)
except* TypeError as eg:
    errors.extend(eg.exceptions)
assert len(errors) == 2
print("OK: except* — splits and handles both types")
""")
else:
    print("OK: except* — skipped (< 3.11)")
