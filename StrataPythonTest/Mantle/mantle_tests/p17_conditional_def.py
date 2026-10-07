# A `def` under `if` binds the module global when it runs.
import sys

if sys.platform == "win32":
    def f():
        return 1
else:
    def f():
        return 2

try:
    def g():
        return f()
except Exception:
    g = None
