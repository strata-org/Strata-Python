from typing import Dict

def dup_binder(d: Dict[str, str]) -> None:
    for k, k in d.items():
        assert k != "bad", "no value is bad"

def dup_binder_all(d: Dict[str, str]) -> None:
    assert all(k != "bad" for k, k in d.items()), "no value is bad"
