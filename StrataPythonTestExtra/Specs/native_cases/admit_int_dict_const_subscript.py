# A constant-key subscript on a non-str-keyed dict is dropped, matching the
# dynamic-key branch.
from typing import Dict


@admit(lambda d, result: d["x"] >= 0)
def f(d: Dict[int, int]) -> int:
    ...
