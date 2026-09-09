# Dict frame axiom missing — `d["x"]=5; d["y"]` must still return old value;
# setting one key destroys knowledge of all others
"""
DICT FRAME AXIOM — SET AT ONE KEY PRESERVES OTHER KEYS

CPython: d = {"x": 1, "y": 2}; d["x"] = 99; d["y"] == 2 (unchanged!)

Model:   d' = DictStrAny_set(d, "x", 99)
         DictStrAny_get(d', "y") == ???

         Finding 254 covers: get(set(d, k, v), k) == v (same key)
         This finding covers: get(set(d, k, v), k2) == get(d, k2) for k≠k2

         Without the frame axiom, setting "x" makes "y" unconstrained.
         The solver cannot prove d["y"] is preserved after d["x"] = 99.

This is the DICT parallel of finding 365 (list frame axiom).
"""


def set_preserves_other() -> bool:
    """Setting one key must not affect another."""
    d: dict[str, int] = {"x": 1, "y": 2, "z": 3}
    d["x"] = 99
    # CPython: d["y"] still 2, d["z"] still 3
    # Model without frame axiom: d["y"] and d["z"] unconstrained
    return d["y"] == 2 and d["z"] == 3


def multiple_sets_preserve() -> bool:
    """Multiple sets, each preserving unrelated keys."""
    d: dict[str, int] = {"a": 1, "b": 2, "c": 3}
    d["a"] = 10
    d["b"] = 20
    # After both sets: d["c"] must still be 3
    # Requires frame axiom applied twice:
    #   get(set(set(d,"a",10),"b",20),"c") == get(set(d,"a",10),"c") == get(d,"c") == 3
    return d["c"] == 3


def build_then_read_all() -> bool:
    """Build dict incrementally, read all keys."""
    d: dict[str, int] = {}
    d["host"] = 1
    d["port"] = 2
    d["timeout"] = 3
    # Each set must preserve previously-set keys
    # d["host"] requires: frame through port-set AND timeout-set
    return d["host"] == 1 and d["port"] == 2 and d["timeout"] == 3


def config_update(d: dict[str, int], key: str, value: int) -> dict[str, int]:
    """Update one key, return dict with all others preserved."""
    d[key] = value
    return d


def main() -> None:
    assert set_preserves_other()
    assert multiple_sets_preserve()
    assert build_then_read_all()

    # Test config update preserves other keys
    cfg: dict[str, int] = {"port": 8080, "timeout": 30, "retries": 3}
    cfg = config_update(cfg, "timeout", 60)
    assert cfg["port"] == 8080      # preserved
    assert cfg["timeout"] == 60     # updated
    assert cfg["retries"] == 3      # preserved

    print("all passed")


main()
