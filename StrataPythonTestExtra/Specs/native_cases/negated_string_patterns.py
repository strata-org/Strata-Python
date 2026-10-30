# PySpec reads `x != "A"` as `not (x == "A")`, and `"k" not in d` as `not ("k" in d)`, also
# inside a quantifier and as the condition of an `if`.
from typing import Dict, List

def f(region: str, tags: Dict[str, str], names: List[str], n: int) -> None:
    assert region != "local", "region must not be local"
    assert "secret" not in tags, "tags must not have a secret key"
    assert all(t != "" for t in names), "names must not be empty strings"
    if region != "local":
        assert n >= 1, "n must be positive outside local"
