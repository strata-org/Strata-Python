# Native @admit acknowledged postcondition decorator (with the `result` binder).
@admit(lambda result: result >= 0)
def f(x: int) -> int:
    ...
