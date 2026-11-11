# exit is an instance of a built-in type whose instances have a __dict__, which CPython writes; the
# model holds no dict for it, so the write stops with a gap.
exit.x = 1
print(exit.x)
