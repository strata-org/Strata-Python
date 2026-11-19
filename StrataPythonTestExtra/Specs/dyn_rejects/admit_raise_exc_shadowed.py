from typing import List

# The generator-local exc shadows the raised exception.
@admit_raise(lambda exc, xs: OLD(any(exc >= 0 for exc in xs)))
def f(xs: List[int]) -> int:
    ...
