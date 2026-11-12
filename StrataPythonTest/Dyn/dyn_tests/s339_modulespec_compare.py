# A ModuleSpec's __eq__ is Python code that reads the other operand's attributes, so CPython's ==
# of builtins.__spec__ and an object with the same attributes is True; the model doesn't follow
# that code, so the run stops with a gap.
import builtins
class N:
    name = "builtins"
    loader = builtins.__loader__
    origin = "built-in"
    submodule_search_locations = None
    cached = None
    has_location = False
s = builtins.__spec__
print(type(s).__name__)
for f in [lambda: s == N(), lambda: N() == s, lambda: s != N(), lambda: N() != s]:
    print(f())
class X(Exception):
    pass
print(s == X())
