# CPython runs the decorators of a definition that a later definition of the same name replaces.
@ghost(name="g", type=int, init=len("ab"))
def f(x: int) -> int:
    ...

def f(x: int) -> int:
    ...
