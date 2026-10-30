# isinstance of a name that is a parameter rejects the model.
@requires(lambda x, T: isinstance(x, T))
def f(x: int, T: int) -> None:
    ...
