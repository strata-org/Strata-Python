# OLD(result) must be a hard error (result doesn't exist in the pre-state).
@admit(lambda x, result: OLD(result) >= 0)
def f(x: int) -> int:
    ...
