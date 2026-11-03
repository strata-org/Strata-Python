# CPython evaluates the init= of a function's ghost when it imports the model.
@ghost(name="g", init=len("ab"))
def f(x: int) -> None:
    ...

@ghost(name="h", init=0)
def literal(x: int) -> None:
    ...

@ghost(name="n", init=-1)
def negative(x: int) -> None:
    ...

@ghost(name="m", init=-None)
def negated_none(x: int) -> None:
    ...
