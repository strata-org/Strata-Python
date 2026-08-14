from typing import List

# The generator-local result shadows the post-state result binder.
@admit(lambda xs, result: OLD(any(result >= 0 for result in xs)))
def f(xs: List[int]) -> int:
    ...
