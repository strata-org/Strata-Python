# A second binding of the typing module name rejects the model.
import typing
typing = int


def f(a: typing.Optional[int]) -> None:
    ...
