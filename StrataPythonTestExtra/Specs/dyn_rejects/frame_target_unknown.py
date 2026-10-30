# A @modifies target that is neither a parameter nor a ghost rejects the model.
@modifies(lambda: elsewhere)
def f() -> None:
    ...
