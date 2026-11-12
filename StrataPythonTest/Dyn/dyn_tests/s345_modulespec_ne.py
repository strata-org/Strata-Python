# != with a ModuleSpec runs object.__ne__, which calls ModuleSpec's own __eq__, Python code that
# reads the other operand's attributes; the model stops with a gap.
import builtins
class N:
    name = "builtins"
    loader = builtins.__loader__
    origin = "built-in"
    submodule_search_locations = None
    cached = None
    has_location = False
s = builtins.__spec__
print(s != N())
print(N() != s)
