from typing import Dict

# Dict[int, _] cannot be represented by the string-key logical map.
@requires(lambda D: all(len(v) >= 1 for v in D.values()))
def f(D: Dict[int, str]) -> None:
    ...
