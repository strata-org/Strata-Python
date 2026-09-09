# NAIVE MODEL WOULD GET WRONG: binds the leaf module for dotted import
import os.path
# Naive: 'os.path' bound as a single name. CPython: 'os' bound (top-level package)
assert "os" in dir()
# The leaf is accessible via attribute, not as a standalone name
assert hasattr(os, "path")
print("BOUNDARY: naive model binds leaf; CPython binds top-level package only")
