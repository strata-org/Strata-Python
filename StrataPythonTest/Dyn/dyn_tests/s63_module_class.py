# Test: a module's __class__ is its type
import builtins
print(builtins.__class__ is type(builtins))
