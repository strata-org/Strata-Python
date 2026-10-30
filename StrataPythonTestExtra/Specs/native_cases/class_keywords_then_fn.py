# A class with keywords rejects the model, and the translation goes on after it: the function
# after it is read too, so its own error is reported.
class C(flag=1):
    x: int

def g(x: int, /) -> None:
    ...
