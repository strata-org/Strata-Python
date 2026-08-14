from typing import List

# A quantifier binder does not scope over its iterable.
@admit(lambda result: OLD(any(x >= 0 for x in result)))
def f() -> List[int]:
    ...
