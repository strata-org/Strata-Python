# An @admit whose call means something else in CPython is left out, so f has no admitted
# postcondition.
from typing import Any

@admit(lambda s, len, result: len(s) >= 1)
def f(s: str, len: Any) -> int: ...
