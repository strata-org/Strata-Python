# exit is an instance of a built-in type whose instances have a __dict__, which CPython reads and
# writes; the model holds no dict for it, so the read stops with a gap.
print(type(exit).__name__)
print(exit.name)
