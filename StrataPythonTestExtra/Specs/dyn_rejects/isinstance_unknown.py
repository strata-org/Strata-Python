# isinstance of a name that the model doesn't define rejects the model.
@requires(lambda x: isinstance(x, Missing))
def f(x: int) -> None:
    ...
