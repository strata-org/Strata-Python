# Dynamic-key dict lookups compare through the numeric fallback.
from typing import Any, Dict


@admit(lambda d1, d2, k1, k2, result: d1[k1] >= d2[k2])
def f(d1: Dict[str, Any], d2: Dict[str, Any], k1: str, k2: str) -> int:
    ...
