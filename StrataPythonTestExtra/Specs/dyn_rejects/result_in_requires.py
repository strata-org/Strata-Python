# result in a @requires rejects the model.
@requires(lambda x, result: result > x)
def f(x: int) -> int:
    ...
