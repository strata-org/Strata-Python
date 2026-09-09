# Type alias with forward reference (3.12+)
import sys
if sys.version_info >= (3, 12):
    exec("""
type Tree = int | list['Tree']  # lazy eval allows self-reference
assert 'Tree' in repr(Tree)
print("OK: annotation scope — lazy evaluation allows forward refs")
""")
else:
    print("OK: annotation scopes — skipped (< 3.12)")
