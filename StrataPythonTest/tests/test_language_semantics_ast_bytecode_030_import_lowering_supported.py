# Import binds the top-level package name
import os.path
assert hasattr(os, 'path')
# 'os' is bound, not 'os.path' directly
print("OK: import lowering — top-level package bound")
