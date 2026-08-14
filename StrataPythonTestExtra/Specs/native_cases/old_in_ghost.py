# A ghost initializer has no post-state in which OLD could be interpreted.
@ghost(name="g", init=OLD(x))
def f(x: int) -> int:
    ...
