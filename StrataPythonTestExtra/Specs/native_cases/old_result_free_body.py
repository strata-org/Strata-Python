from typing import List

# The result used in the body is the post-state binder, not the loop variable.
@admit(lambda xs, result: OLD(any(x >= result for x in xs)))
def f(xs: List[int]) -> int:
    ...
